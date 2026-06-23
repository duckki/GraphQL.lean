import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.DepthZero
import GraphQL.Execution.ResolverValue

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

inductive ValueContainsObject {ObjectIdentity : Type} :
    ResolverValue ObjectIdentity -> Name -> ObjectIdentity -> Prop where
  | here {runtimeType : Name} {identity : ObjectIdentity} :
      ValueContainsObject (.object runtimeType identity) runtimeType identity
  | list {values : List (ResolverValue ObjectIdentity)} {value : ResolverValue ObjectIdentity}
      {runtimeType : Name} {identity : ObjectIdentity} :
      value ∈ values ->
      ValueContainsObject value runtimeType identity ->
        ValueContainsObject (.list values) runtimeType identity

theorem completeResolvedValue_none_eq_completeValue
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) :
    ∀ (fieldType : TypeRef) (selectionSet : List Selection)
      (value : ResolverValue ObjectIdentity),
      completeResolvedValue schema resolvers variableValues depth fieldType
        selectionSet value none =
      completeValue schema resolvers variableValues depth fieldType
        selectionSet value none := by
  intro fieldType
  induction fieldType with
  | named typeName =>
      intro selectionSet value
      simp [completeResolvedValue, reusablePreviousValue?_none]
  | list inner ih =>
      intro selectionSet value
      simp [completeResolvedValue, reusablePreviousValue?_none]
  | nonNull inner ih =>
      intro selectionSet value
      cases depth with
      | zero =>
          simp [completeResolvedValue, reusablePreviousValue?_none]
          rw [ih selectionSet value]
          cases value <;>
            simp [completeValue, outOfFuel, nonNullCompletion]
      | succ depth' =>
        simp [completeResolvedValue, completeValue,
          reusablePreviousValue?_none, ih selectionSet value]

theorem resultCombine_append_assoc {α : Type}
    (left middle right : Result (List α)) :
    Result.combine List.append
        (Result.combine List.append left middle) right =
      Result.combine List.append left
        (Result.combine List.append middle right) := by
  cases left with
  | error leftErrors =>
      cases middle with
      | error middleErrors =>
          cases right with
          | error rightErrors =>
              simp [GraphQL.Execution.Result.combine,
                Nat.add_assoc]
          | ok rightResult =>
              rcases rightResult with ⟨rightFields, rightErrors⟩
              simp [GraphQL.Execution.Result.combine,
                Nat.add_assoc]
      | ok middleResult =>
          rcases middleResult with ⟨middleFields, middleErrors⟩
          cases right with
          | error rightErrors =>
              simp [GraphQL.Execution.Result.combine,
                Nat.add_assoc]
          | ok rightResult =>
              rcases rightResult with ⟨rightFields, rightErrors⟩
              simp [GraphQL.Execution.Result.combine,
                Nat.add_assoc]
  | ok leftResult =>
      rcases leftResult with ⟨leftFields, leftErrors⟩
      cases middle with
      | error middleErrors =>
          cases right with
          | error rightErrors =>
              simp [GraphQL.Execution.Result.combine,
                Nat.add_assoc]
          | ok rightResult =>
              rcases rightResult with ⟨rightFields, rightErrors⟩
              simp [GraphQL.Execution.Result.combine,
                Nat.add_assoc]
      | ok middleResult =>
          rcases middleResult with ⟨middleFields, middleErrors⟩
          cases right with
          | error rightErrors =>
              simp [GraphQL.Execution.Result.combine,
                Nat.add_assoc]
          | ok rightResult =>
              rcases rightResult with ⟨rightFields, rightErrors⟩
              simp [GraphQL.Execution.Result.combine,
                List.append_assoc, Nat.add_assoc]

theorem specExecuteCollectedFields_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity) :
    ∀ left right : List (Name × List ExecutableField),
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        depth source (left ++ right) =
      Result.combine List.append
        (GraphQL.Execution.executeCollectedFields schema resolvers
          variableValues depth source left)
        (GraphQL.Execution.executeCollectedFields schema resolvers
          variableValues depth source right)
  | [], right => by
      cases hright :
          GraphQL.Execution.executeCollectedFields schema resolvers
            variableValues depth source right with
      | error rightErrors =>
          simp [GraphQL.Execution.executeCollectedFields, Result.combine,
            GraphQL.Execution.Result.combine, hright]
      | ok rightResult =>
          rcases rightResult with ⟨rightFields, rightErrors⟩
          simp [GraphQL.Execution.executeCollectedFields, Result.combine,
            GraphQL.Execution.Result.combine, hright]
  | (responseName, fields) :: rest, right => by
      simp [GraphQL.Execution.executeCollectedFields,
        specExecuteCollectedFields_append schema resolvers variableValues depth
          source rest right]
      rw [resultCombine_append_assoc]

theorem specExecuteRootSelectionSet_append_of_namesDisjoint
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
          source right)) :
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source (left ++ right) =
    Result.combine List.append
      (GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source left)
      (GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source right) := by
  simp [GraphQL.Execution.executeRootSelectionSet]
  rw [GraphQL.NormalForm.collectFields_append]
  rw [GraphQL.NormalForm.mergeExecutableGroups_eq_append_of_namesDisjoint]
  · exact specExecuteCollectedFields_append schema resolvers variableValues
      depth source
      (GraphQL.Execution.collectFields schema variableValues parentType source
        left)
      (GraphQL.Execution.collectFields schema variableValues parentType source
        right)
  · exact hdisjoint
  · exact GraphQL.NormalForm.collectFields_namesNodup schema variableValues
      parentType source right

theorem resultValueOrNull_eq_result_getD
    (completed : Result ResponseValue) :
    resultValueOrNull completed =
      GraphQL.Execution.Result.getD .null completed := by
  cases completed with
  | error errors =>
      rfl
  | ok result =>
      rcases result with ⟨value, errors⟩
      rfl

theorem executeField_key_mem
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity) :
    ∀ {responseName groupName fields},
      responseName ∈
        (GraphQL.Execution.executeFieldData schema resolvers variableValues
          depth source groupName fields).map Prod.fst ->
      responseName = groupName
  | _responseName, _groupName, [], hmem => by
      simp [GraphQL.Execution.executeFieldData, GraphQL.Execution.executeField,
        GraphQL.Execution.Result.getD] at hmem
  | _responseName, _groupName, field :: fields, hmem => by
      cases depth with
      | zero =>
          simp [GraphQL.Execution.executeFieldData,
            GraphQL.Execution.executeField, GraphQL.Execution.Result.getD,
            outOfFuel] at hmem
      | succ depth' =>
          cases hlookup :
              schema.lookupField field.parentType field.fieldName with
          | none =>
              simp [GraphQL.Execution.executeFieldData,
                GraphQL.Execution.executeField, GraphQL.Execution.Result.getD,
                hlookup] at hmem
          | some fieldDefinition =>
              cases hresolve :
                  resolvers.resolve field.parentType field.fieldName
                    field.arguments source with
              | none =>
                  cases hcompleted :
                      GraphQL.Execution.handleFieldError
                        fieldDefinition.outputType with
                  | error errors =>
                      simp [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.executeField,
                        GraphQL.Execution.singleFieldResult,
                        GraphQL.Execution.Result.getD, hlookup, hresolve,
                        hcompleted] at hmem
                  | ok result =>
                      rcases result with ⟨response, errors⟩
                      simpa [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.executeField,
                        GraphQL.Execution.singleFieldResult,
                        GraphQL.Execution.Result.getD, hlookup, hresolve,
                        hcompleted] using hmem
              | some resolved =>
                  cases hcompleted :
                      GraphQL.Execution.completeValue schema resolvers
                        variableValues depth' fieldDefinition.outputType
                        (field :: fields) resolved with
                  | error errors =>
                      simp [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.executeField,
                        GraphQL.Execution.singleFieldResult,
                        GraphQL.Execution.Result.getD, hlookup, hresolve,
                        hcompleted] at hmem
                  | ok result =>
                      rcases result with ⟨response, errors⟩
                      simpa [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.executeField,
                        GraphQL.Execution.singleFieldResult,
                        GraphQL.Execution.Result.getD, hlookup, hresolve,
                        hcompleted] using hmem

theorem executeCollectedFields_key_mem
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity) :
    ∀ {responseName groups},
      responseName ∈
        (GraphQL.Execution.executeCollectedFieldsData schema resolvers
          variableValues depth source groups).map Prod.fst ->
      responseName ∈ groups.map Prod.fst
  | _responseName, [], hmem => by
      simp [GraphQL.Execution.executeCollectedFieldsData,
        GraphQL.Execution.executeCollectedFields, GraphQL.Execution.Result.getD]
        at hmem
  | responseName, (groupName, fields) :: rest, hmem => by
      cases hhead :
          GraphQL.Execution.executeField schema resolvers variableValues depth
            source groupName fields with
      | error headErrors =>
          cases htail :
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues depth source rest with
          | error tailErrors =>
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, hhead, htail] at hmem
          | ok tailResult =>
              rcases tailResult with ⟨tailFields, tailErrors⟩
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, hhead, htail] at hmem
      | ok headResult =>
          rcases headResult with ⟨headFields, headErrors⟩
          cases htail :
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues depth source rest with
          | error tailErrors =>
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, hhead, htail] at hmem
          | ok tailResult =>
              rcases tailResult with ⟨tailFields, tailErrors⟩
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, hhead, htail] at hmem
              rcases hmem with hheadMem | htailMem
              · have hkey :
                    responseName = groupName :=
                  executeField_key_mem schema resolvers variableValues depth
                    source (responseName := responseName)
                    (groupName := groupName) (fields := fields) <| by
                      simpa [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.Result.getD, hhead] using hheadMem
                subst responseName
                simp
              · right
                apply executeCollectedFields_key_mem schema resolvers
                  variableValues depth source
                simpa [GraphQL.Execution.executeCollectedFieldsData,
                  GraphQL.Execution.Result.getD, htail] using htailMem

theorem executeField_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity)
    (groupName : Name) (fields : List ExecutableField) :
    PairKeysNodup
      (GraphQL.Execution.executeFieldData schema resolvers variableValues
        depth source groupName fields) := by
  unfold PairKeysNodup
  cases fields with
  | nil =>
      simp [GraphQL.Execution.executeFieldData, GraphQL.Execution.executeField,
        GraphQL.Execution.Result.getD]
  | cons field rest =>
      cases depth with
      | zero =>
          simp [GraphQL.Execution.executeFieldData,
            GraphQL.Execution.executeField, GraphQL.Execution.Result.getD,
            outOfFuel]
      | succ depth' =>
          cases hlookup :
              schema.lookupField field.parentType field.fieldName with
          | none =>
              simp [GraphQL.Execution.executeFieldData,
                GraphQL.Execution.executeField, GraphQL.Execution.Result.getD,
                hlookup]
          | some fieldDefinition =>
              cases hresolve :
                  resolvers.resolve field.parentType field.fieldName
                    field.arguments source with
              | none =>
                  cases hcompleted :
                      GraphQL.Execution.handleFieldError
                        fieldDefinition.outputType with
                  | error errors =>
                      simp [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.executeField,
                        GraphQL.Execution.singleFieldResult,
                        GraphQL.Execution.Result.getD, hlookup, hresolve,
                        hcompleted]
                  | ok result =>
                      rcases result with ⟨response, errors⟩
                      simp [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.executeField,
                        GraphQL.Execution.singleFieldResult,
                        GraphQL.Execution.Result.getD, hlookup, hresolve,
                        hcompleted]
              | some resolved =>
                  cases hcompleted :
                      GraphQL.Execution.completeValue schema resolvers
                        variableValues depth' fieldDefinition.outputType
                        (field :: rest) resolved with
                  | error errors =>
                      simp [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.executeField,
                        GraphQL.Execution.singleFieldResult,
                        GraphQL.Execution.Result.getD, hlookup, hresolve,
                        hcompleted]
                  | ok result =>
                      rcases result with ⟨response, errors⟩
                      simp [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.executeField,
                        GraphQL.Execution.singleFieldResult,
                        GraphQL.Execution.Result.getD, hlookup, hresolve,
                        hcompleted]

theorem specExecuteRootSelectionSet_key_mem
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) (responseName : Name) :
    responseName ∈
        (GraphQL.Execution.executeRootSelectionSetData schema resolvers
          variableValues depth parentType source selectionSet).map Prod.fst ->
      responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType
          source selectionSet).map Prod.fst := by
  intro hmem
  simpa [GraphQL.Execution.executeRootSelectionSetData] using
    executeCollectedFields_key_mem schema resolvers variableValues depth source
      hmem

theorem executeRootSelectionSet_key_mem_of_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) (responseName : Name)
      (hroot :
        executeRootSelectionSet schema resolvers variableValues depth parentType
          source selectionSet =
        GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source selectionSet) :
      responseName ∈
          (GraphQL.Execution.Result.getD []
            (executeRootSelectionSet schema resolvers variableValues depth
              parentType source selectionSet)).map Prod.fst ->
        responseName ∈
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet).map Prod.fst := by
    intro hmem
    apply specExecuteRootSelectionSet_key_mem schema resolvers variableValues
      depth parentType source selectionSet responseName
    simpa [hroot, GraphQL.Execution.executeRootSelectionSetData] using hmem

theorem responseName_fresh_of_disjoint_single_field
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
      (hleftEq :
        executeRootSelectionSet schema resolvers variableValues depth parentType
          source left =
        GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source left)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType
          source
          [.field responseName fieldName arguments directives selectionSet]))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
      responseName ∉
        (GraphQL.Execution.Result.getD []
          (executeRootSelectionSet schema resolvers variableValues depth
            parentType source left)).map Prod.fst := by
  intro hmem
  have hleftMem :
      responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left).map Prod.fst :=
    executeRootSelectionSet_key_mem_of_eq_spec schema resolvers variableValues
      depth parentType source left responseName hleftEq hmem
  have hrightMem :
      responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType
          source
          [.field responseName fieldName arguments directives selectionSet]).map
          Prod.fst := by
    simp [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups,
      hallowed]
  exact hdisjoint responseName hleftMem hrightMem

theorem visitSubfields_object_empty_key_mem_collectFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) (fields : List (Name × ResponseValue))
    (responseName : Name) :
      (visitSubfields schema resolvers variableValues depth parentType source
        selectionSet (.object [])).fst = .object fields ->
    responseName ∈ fields.map Prod.fst ->
      responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet).map Prod.fst := by
  intro hvisit hmem
  by_cases hcollect :
      responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet).map Prod.fst
  · exact hcollect
  have hpreserve :=
    visitSubfields_responseObjectField?_of_not_mem_collectFields schema
      resolvers variableValues depth parentType source responseName selectionSet
      (.object []) hcollect
  rw [hvisit] at hpreserve
  rcases lookupResponseField?_some_of_mem responseName fields hmem with
    ⟨response, hlookup⟩
  simp [responseObjectField?, lookupResponseField?, hlookup] at hpreserve

theorem responseName_fresh_of_disjoint_single_field_visitSubfields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType
          source
          [.field responseName fieldName arguments directives selectionSet]))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
      ∀ fields status,
        visitSubfields schema resolvers variableValues depth parentType source
          left (.object []) = (.object fields, status) ->
        responseName ∉ fields.map Prod.fst := by
  intro fields status hvisit hmem
  have hleftMem :
      responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left).map Prod.fst :=
    visitSubfields_object_empty_key_mem_collectFields schema resolvers
      variableValues depth parentType source left fields responseName
      (by simp [hvisit]) hmem
  have hrightMem :
      responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType
          source
          [.field responseName fieldName arguments directives selectionSet]).map
          Prod.fst := by
    simp [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups,
      hallowed]
  exact hdisjoint responseName hleftMem hrightMem

theorem executableGroupNamesDisjoint_single_field_of_responseName_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh :
      responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left).map Prod.fst) :
    GraphQL.NormalForm.executableGroupNamesDisjoint
      (GraphQL.Execution.collectFields schema variableValues parentType
        source left)
      (GraphQL.Execution.collectFields schema variableValues parentType source
        [.field responseName fieldName arguments directives selectionSet]) := by
  intro candidate hleft hright
  simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
    GraphQL.Execution.mergeExecutableGroups, hallowed] at hright
  exact hfresh (by simpa [hright] using hleft)

theorem executeCollectedFields_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity) :
    ∀ groups,
      PairKeysNodup groups ->
        PairKeysNodup
          (GraphQL.Execution.executeCollectedFieldsData schema resolvers
            variableValues depth source groups)
  | [], _hnodup => by
      simp [GraphQL.Execution.executeCollectedFieldsData,
        GraphQL.Execution.executeCollectedFields, GraphQL.Execution.Result.getD,
        PairKeysNodup]
  | (groupName, fields) :: rest, hnodup => by
      have hrestNodup : PairKeysNodup rest :=
        PairKeysNodup.tail hnodup
      cases hhead :
          GraphQL.Execution.executeField schema resolvers variableValues depth
            source groupName fields with
      | error headErrors =>
          cases htail :
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues depth source rest with
          | error tailErrors =>
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, PairKeysNodup, hhead, htail]
          | ok tailResult =>
              rcases tailResult with ⟨tailFields, tailErrors⟩
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, PairKeysNodup, hhead, htail]
      | ok headResult =>
          rcases headResult with ⟨headFields, headErrors⟩
          cases htail :
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues depth source rest with
          | error tailErrors =>
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, PairKeysNodup, hhead, htail]
          | ok tailResult =>
              rcases tailResult with ⟨tailFields, tailErrors⟩
              have hheadNodup : PairKeysNodup headFields := by
                simpa [GraphQL.Execution.executeFieldData,
                  GraphQL.Execution.Result.getD, hhead] using
                  executeField_pairKeysNodup schema resolvers variableValues
                    depth source groupName fields
              have htailNodup : PairKeysNodup tailFields := by
                simpa [GraphQL.Execution.executeCollectedFieldsData,
                  GraphQL.Execution.Result.getD, htail] using
                  executeCollectedFields_pairKeysNodup schema resolvers
                    variableValues depth source rest hrestNodup
              have hdisjoint :
                  ∀ responseName,
                    responseName ∈ headFields.map Prod.fst ->
                      responseName ∉ tailFields.map Prod.fst := by
                intro responseName hheadMem htailMem
                have hheadKey :
                    responseName = groupName :=
                  executeField_key_mem schema resolvers variableValues depth
                    source (responseName := responseName)
                    (groupName := groupName) (fields := fields) <| by
                      simpa [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.Result.getD, hhead] using hheadMem
                have htailKey :
                    responseName ∈ rest.map Prod.fst :=
                  executeCollectedFields_key_mem schema resolvers
                    variableValues depth source <| by
                      simpa [GraphQL.Execution.executeCollectedFieldsData,
                        GraphQL.Execution.Result.getD, htail] using htailMem
                rw [hheadKey] at htailKey
                exact PairKeysNodup.head_not_mem_tail hnodup htailKey
              simpa [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, hhead, htail] using
                PairKeysNodup.append hheadNodup htailNodup hdisjoint

theorem collectFields_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    PairKeysNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet) :=
  PairKeysNodup_of_executableGroupNamesNodup
    (GraphQL.Execution.collectFields schema variableValues parentType source
      selectionSet)
    (NormalForm.collectFields_namesNodup schema variableValues parentType
      source selectionSet)

theorem collectSubfields_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (objectType : Name) (objectValue : ResolverValue ObjectIdentity)
    (fields : List ExecutableField) :
    PairKeysNodup
      (GraphQL.Execution.collectSubfields schema variableValues objectType
        objectValue fields) := by
  simpa [GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
    using
      collectFields_pairKeysNodup schema variableValues objectType objectValue
        (GraphQL.Execution.mergedFieldSelectionSet fields)

mutual
  theorem specExecuteCollectedFields_response_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (source : ResolverValue ObjectIdentity) :
      ∀ groups,
        PairKeysNodup groups ->
          ResponseMergeReady
            (.object
              (GraphQL.Execution.executeCollectedFieldsData schema resolvers
                variableValues depth source groups))
      | [], _hnodup => by
          simpa [GraphQL.Execution.executeCollectedFieldsData,
            GraphQL.Execution.executeCollectedFields,
            GraphQL.Execution.Result.getD] using
            ResponseMergeReady_empty_object
      | (groupName, fields) :: rest, hnodup => by
          have hrestNodup : PairKeysNodup rest :=
            PairKeysNodup.tail hnodup
          cases hhead :
              GraphQL.Execution.executeField schema resolvers variableValues depth
                source groupName fields with
          | error headErrors =>
              cases htail :
                  GraphQL.Execution.executeCollectedFields schema resolvers
                    variableValues depth source rest with
              | error tailErrors =>
                  simpa [GraphQL.Execution.executeCollectedFieldsData,
                    GraphQL.Execution.executeCollectedFields,
                    GraphQL.Execution.Result.combine,
                    GraphQL.Execution.Result.combine,
                    GraphQL.Execution.Result.getD, hhead, htail] using
                    ResponseMergeReady_empty_object
              | ok tailResult =>
                  rcases tailResult with ⟨tailFields, tailErrors⟩
                  simpa [GraphQL.Execution.executeCollectedFieldsData,
                    GraphQL.Execution.executeCollectedFields,
                    GraphQL.Execution.Result.combine,
                    GraphQL.Execution.Result.combine,
                    GraphQL.Execution.Result.getD, hhead, htail] using
                    ResponseMergeReady_empty_object
          | ok headResult =>
              rcases headResult with ⟨headFields, headErrors⟩
              cases htail :
                  GraphQL.Execution.executeCollectedFields schema resolvers
                    variableValues depth source rest with
              | error tailErrors =>
                  simpa [GraphQL.Execution.executeCollectedFieldsData,
                    GraphQL.Execution.executeCollectedFields,
                    GraphQL.Execution.Result.combine,
                    GraphQL.Execution.Result.combine,
                    GraphQL.Execution.Result.getD, hhead, htail] using
                    ResponseMergeReady_empty_object
              | ok tailResult =>
                  rcases tailResult with ⟨tailFields, tailErrors⟩
                  have hheadReady : ResponseMergeReady (.object headFields) := by
                    simpa [GraphQL.Execution.executeFieldData,
                      GraphQL.Execution.Result.getD, hhead] using
                      specExecuteField_response_ready schema resolvers
                        variableValues depth source groupName fields
                  have htailReady : ResponseMergeReady (.object tailFields) := by
                    simpa [GraphQL.Execution.executeCollectedFieldsData,
                      GraphQL.Execution.Result.getD, htail] using
                      specExecuteCollectedFields_response_ready schema resolvers
                        variableValues depth source rest hrestNodup
                  have hdisjoint :
                      ∀ responseName,
                        responseName ∈ headFields.map Prod.fst ->
                          responseName ∉ tailFields.map Prod.fst := by
                    intro responseName hheadMem htailMem
                    have hheadKey :
                        responseName = groupName :=
                      executeField_key_mem schema resolvers variableValues depth
                        source (responseName := responseName)
                        (groupName := groupName) (fields := fields) <| by
                          simpa [GraphQL.Execution.executeFieldData,
                            GraphQL.Execution.Result.getD, hhead] using hheadMem
                    have htailKey :
                        responseName ∈ rest.map Prod.fst :=
                      executeCollectedFields_key_mem schema resolvers
                        variableValues depth source <| by
                          simpa [GraphQL.Execution.executeCollectedFieldsData,
                            GraphQL.Execution.Result.getD, htail] using htailMem
                    rw [hheadKey] at htailKey
                    exact PairKeysNodup.head_not_mem_tail hnodup htailKey
                  simpa [GraphQL.Execution.executeCollectedFieldsData,
                    GraphQL.Execution.executeCollectedFields,
                    GraphQL.Execution.Result.combine,
                    GraphQL.Execution.Result.combine,
                    GraphQL.Execution.Result.getD, hhead, htail] using
                    ResponseMergeReady_object_append headFields tailFields
                      hheadReady htailReady
                      (by
                        intro responseName htailMem hheadMem
                        exact hdisjoint responseName hheadMem htailMem)

  theorem specExecuteField_response_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (source : ResolverValue ObjectIdentity) :
      ∀ responseName fields,
        ResponseMergeReady
          (.object
            (GraphQL.Execution.executeFieldData schema resolvers variableValues
              depth source responseName fields))
      | _responseName, [] => by
          simpa [GraphQL.Execution.executeFieldData,
            GraphQL.Execution.executeField, GraphQL.Execution.Result.getD] using
            ResponseMergeReady_empty_object
      | responseName, field :: rest => by
          cases depth with
          | zero =>
              simpa [GraphQL.Execution.executeFieldData,
                GraphQL.Execution.executeField, GraphQL.Execution.Result.getD] using
                ResponseMergeReady_empty_object
          | succ depth' =>
              cases hlookup :
                  schema.lookupField field.parentType field.fieldName with
              | none =>
                  simpa [GraphQL.Execution.executeFieldData,
                    GraphQL.Execution.executeField, GraphQL.Execution.Result.getD,
                    hlookup] using
                    ResponseMergeReady_empty_object
              | some fieldDefinition =>
                  cases hresolve :
                      resolvers.resolve field.parentType field.fieldName
                        field.arguments source with
                  | none =>
                      cases hcompleted :
                          GraphQL.Execution.handleFieldError
                            fieldDefinition.outputType with
                      | error errors =>
                          simpa [GraphQL.Execution.executeFieldData,
                            GraphQL.Execution.executeField,
                            GraphQL.Execution.singleFieldResult,
                            GraphQL.Execution.Result.getD, hlookup, hresolve,
                            hcompleted] using
                            ResponseMergeReady_empty_object
                      | ok result =>
                          rcases result with ⟨response, errors⟩
                          have hresponseReady : ResponseMergeReady response := by
                            simpa [resultValueOrNull, hcompleted] using
                              resultValueOrNull_handleFieldError_ready
                                fieldDefinition.outputType
                          simpa [GraphQL.Execution.executeFieldData,
                            GraphQL.Execution.executeField,
                            GraphQL.Execution.singleFieldResult,
                            GraphQL.Execution.Result.getD, hlookup, hresolve,
                            hcompleted] using
                            ResponseMergeReady.object [(responseName, response)]
                              (by simp [PairKeysNodup])
                              (by
                                intro candidate candidateResponse hmem
                                simp at hmem
                                rcases hmem with ⟨rfl, rfl⟩
                                exact hresponseReady)
                  | some resolved =>
                      cases hcompleted :
                          GraphQL.Execution.completeValue schema resolvers
                            variableValues depth' fieldDefinition.outputType
                            (field :: rest) resolved with
                      | error errors =>
                          simpa [GraphQL.Execution.executeFieldData,
                            GraphQL.Execution.executeField,
                            GraphQL.Execution.singleFieldResult,
                            GraphQL.Execution.Result.getD, hlookup, hresolve,
                            hcompleted] using
                            ResponseMergeReady_empty_object
                      | ok result =>
                          rcases result with ⟨response, errors⟩
                          have hresponseReady : ResponseMergeReady response := by
                            simpa [GraphQL.Execution.completeValueData,
                              GraphQL.Execution.Result.getD, hcompleted] using
                              specCompleteValue_response_ready schema resolvers
                                variableValues depth'
                                fieldDefinition.outputType (field :: rest)
                                resolved
                          simpa [GraphQL.Execution.executeFieldData,
                            GraphQL.Execution.executeField,
                            GraphQL.Execution.singleFieldResult,
                            GraphQL.Execution.Result.getD, hlookup, hresolve,
                            hcompleted] using
                            ResponseMergeReady.object [(responseName, response)]
                              (by simp [PairKeysNodup])
                              (by
                                intro candidate candidateResponse hmem
                                simp at hmem
                                rcases hmem with ⟨rfl, rfl⟩
                                exact hresponseReady)

  theorem specCompleteValue_response_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) :
      ∀ (depth : Nat) (fieldType : TypeRef) (fields : List ExecutableField)
        (value : ResolverValue ObjectIdentity),
        ResponseMergeReady
          (GraphQL.Execution.completeValueData schema resolvers variableValues
            depth fieldType fields value)
      | 0, _fieldType, _fields, value => by
          simpa [GraphQL.Execution.completeValueData,
            GraphQL.Execution.completeValue, GraphQL.Execution.outOfFuel,
            GraphQL.Execution.Result.getD] using
            ResponseMergeReady.null
      | depth + 1, .nonNull inner, fields, value => by
          have hinner :
              ResponseMergeReady
                (resultValueOrNull
                  (GraphQL.Execution.completeValue schema resolvers
                    variableValues (depth + 1) inner fields value)) := by
            simpa [GraphQL.Execution.completeValueData,
              resultValueOrNull_eq_result_getD] using
              specCompleteValue_response_ready schema resolvers
                variableValues (depth + 1) inner fields value
          simpa [GraphQL.Execution.completeValueData,
            GraphQL.Execution.completeValue,
            ← resultValueOrNull_eq_result_getD
              (GraphQL.Execution.nonNullCompletion
                (GraphQL.Execution.completeValue schema resolvers variableValues
                  (depth + 1) inner fields value))] using
            resultValueOrNull_nonNullCompletion_ready
              (GraphQL.Execution.completeValue schema resolvers variableValues
                (depth + 1) inner fields value)
              hinner
      | depth + 1, .named typeName, fields, .null => by
          simpa [GraphQL.Execution.completeValueData,
            GraphQL.Execution.completeValue, GraphQL.Execution.Result.getD] using
            ResponseMergeReady.null
      | depth + 1, .named typeName, fields, .scalar value => by
          by_cases hcomposite :
              (TypeRef.named typeName).isCompositeBool schema = true
          · simp [GraphQL.Execution.completeValueData,
              GraphQL.Execution.completeValue, GraphQL.Execution.Result.getD,
              hcomposite]
            exact ResponseMergeReady.null
          · simp [GraphQL.Execution.completeValueData,
              GraphQL.Execution.completeValue, GraphQL.Execution.Result.getD,
              hcomposite]
            exact ResponseMergeReady.scalar value
      | depth + 1, .named typeName, fields,
          .object runtimeType identity => by
          by_cases hinclude :
              schema.typeIncludesObjectBool typeName runtimeType
          · have hgroupsNodup :
                PairKeysNodup
                  (GraphQL.Execution.collectSubfields schema variableValues
                    runtimeType (.object runtimeType identity) fields) :=
              collectSubfields_pairKeysNodup schema variableValues runtimeType
                (.object runtimeType identity) fields
            cases hcompleted :
                GraphQL.Execution.executeCollectedFields schema resolvers
                  variableValues depth (.object runtimeType identity)
                  (GraphQL.Execution.collectSubfields schema variableValues
                    runtimeType (.object runtimeType identity) fields) with
            | error errors =>
                have hcompleted' :
                    GraphQL.Execution.executeCollectedFields schema resolvers
                      variableValues depth (.object runtimeType identity)
                      (GraphQL.Execution.collectFields schema variableValues
                        runtimeType (.object runtimeType identity)
                        (GraphQL.Execution.mergedFieldSelectionSet fields)) =
                    .error errors := by
                  simpa
                    [GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                    using hcompleted
                simpa [GraphQL.Execution.completeValueData,
                  GraphQL.Execution.completeValue, hinclude,
                  GraphQL.Execution.catchBubbleAsNull,
                  GraphQL.Execution.Result.getD, hcompleted',
                  GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                  using
                  ResponseMergeReady.null
            | ok result =>
                rcases result with ⟨completedFields, errors⟩
                have hcompleted' :
                    GraphQL.Execution.executeCollectedFields schema resolvers
                      variableValues depth (.object runtimeType identity)
                      (GraphQL.Execution.collectFields schema variableValues
                        runtimeType (.object runtimeType identity)
                        (GraphQL.Execution.mergedFieldSelectionSet fields)) =
                    .ok (completedFields, errors) := by
                  simpa
                    [GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                    using hcompleted
                have hready :
                    ResponseMergeReady (.object completedFields) := by
                  simpa [GraphQL.Execution.executeCollectedFieldsData,
                    GraphQL.Execution.Result.getD, hcompleted',
                    GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                    using
                    specExecuteCollectedFields_response_ready schema resolvers
                      variableValues depth (.object runtimeType identity)
                      (GraphQL.Execution.collectSubfields schema variableValues
                        runtimeType (.object runtimeType identity) fields)
                      hgroupsNodup
                simpa [GraphQL.Execution.completeValueData,
                  GraphQL.Execution.completeValue, hinclude,
                  GraphQL.Execution.catchBubbleAsNull,
                  GraphQL.Execution.Result.getD, hcompleted',
                  GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                  using hready
          · simpa [GraphQL.Execution.completeValueData,
              GraphQL.Execution.completeValue, hinclude,
              GraphQL.Execution.Result.getD] using
              ResponseMergeReady.null
      | depth + 1, .named typeName, fields, .list values => by
          simpa [GraphQL.Execution.completeValueData,
            GraphQL.Execution.completeValue, GraphQL.Execution.Result.getD] using
            ResponseMergeReady.null
      | depth + 1, .list inner, fields, .null => by
          simpa [GraphQL.Execution.completeValueData,
            GraphQL.Execution.completeValue, GraphQL.Execution.Result.getD] using
            ResponseMergeReady.null
      | depth + 1, .list inner, fields, .scalar value => by
          simpa [GraphQL.Execution.completeValueData,
            GraphQL.Execution.completeValue, GraphQL.Execution.Result.getD] using
            ResponseMergeReady.null
      | depth + 1, .list inner, fields, .object runtimeType identity => by
          simpa [GraphQL.Execution.completeValueData,
            GraphQL.Execution.completeValue, GraphQL.Execution.Result.getD] using
            ResponseMergeReady.null
      | depth + 1, .list inner, fields, .list values => by
          simpa [GraphQL.Execution.completeValueData,
            GraphQL.Execution.completeValue,
            ← resultValueOrNull_eq_result_getD
              (GraphQL.Execution.catchBubbleAsNull ResponseValue.list
                (GraphQL.Execution.completeValueList schema resolvers
                  variableValues depth inner fields values))] using
            resultValueOrNull_catchBubbleAsNull_ready
              ResponseValue.list
              (GraphQL.Execution.completeValueList schema resolvers
                variableValues depth inner fields values)
              (by
                intro completedValues errors hok
                exact ResponseMergeReady.list completedValues
                  (specCompleteValueList_values_ready schema resolvers
                    variableValues depth inner fields values completedValues
                    errors hok))

  theorem specCompleteValueList_values_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) :
      ∀ (depth : Nat) (fieldType : TypeRef)
        (fields : List ExecutableField)
        (values : List (ResolverValue ObjectIdentity))
        (completedValues : List ResponseValue) (errors : Nat),
        GraphQL.Execution.completeValueList schema resolvers variableValues
          depth fieldType fields values = .ok (completedValues, errors) ->
        ∀ response,
          response ∈ completedValues ->
            ResponseMergeReady response
      | _depth, _fieldType, _fields, [], completedValues, errors, hok => by
          intro response hmem
          simp [GraphQL.Execution.completeValueList] at hok
          rcases hok with ⟨hcompletedValues, _herrors⟩
          subst completedValues
          simp at hmem
      | depth, fieldType, fields, value :: values, completedValues, errors,
          hok => by
          cases hhead :
              GraphQL.Execution.completeValue schema resolvers variableValues
                depth fieldType fields value with
          | error headErrors =>
              cases htail :
                  GraphQL.Execution.completeValueList schema resolvers
                    variableValues depth fieldType fields values with
              | error tailErrors =>
                  simp [GraphQL.Execution.completeValueList,
                    GraphQL.Execution.Result.combine,
                    GraphQL.Execution.Result.combine, hhead, htail] at hok
              | ok tailResult =>
                  rcases tailResult with ⟨tailValues, tailErrors⟩
                  simp [GraphQL.Execution.completeValueList,
                    GraphQL.Execution.Result.combine,
                    GraphQL.Execution.Result.combine, hhead, htail] at hok
          | ok headResult =>
              rcases headResult with ⟨headValue, headErrors⟩
              cases htail :
                  GraphQL.Execution.completeValueList schema resolvers
                    variableValues depth fieldType fields values with
              | error tailErrors =>
                  simp [GraphQL.Execution.completeValueList,
                    GraphQL.Execution.Result.combine,
                    GraphQL.Execution.Result.combine, hhead, htail] at hok
              | ok tailResult =>
                  rcases tailResult with ⟨tailValues, tailErrors⟩
                  simp [GraphQL.Execution.completeValueList,
                    GraphQL.Execution.Result.combine,
                    GraphQL.Execution.Result.combine, hhead, htail] at hok
                  rcases hok with ⟨rfl, rfl⟩
                  intro response hmem
                  rcases List.mem_cons.mp hmem with hheadMem | htailMem
                  · subst response
                    simpa [GraphQL.Execution.completeValueData,
                      GraphQL.Execution.Result.getD, hhead] using
                      specCompleteValue_response_ready schema resolvers
                        variableValues depth fieldType fields value
                  · exact
                      specCompleteValueList_values_ready schema resolvers
                        variableValues depth fieldType fields values tailValues
                        tailErrors htail response htailMem
end

theorem specExecuteCollectedFields_collectFields_response_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    ResponseMergeReady
      (.object
        (GraphQL.Execution.executeCollectedFieldsData schema resolvers
          variableValues depth source
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet))) :=
  specExecuteCollectedFields_response_ready schema resolvers variableValues
    depth source
    (GraphQL.Execution.collectFields schema variableValues parentType source
      selectionSet)
    (collectFields_pairKeysNodup schema variableValues parentType source
      selectionSet)

theorem specExecuteRootSelectionSet_response_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    ResponseMergeReady
      (.object
        (GraphQL.Execution.executeRootSelectionSetData schema resolvers
          variableValues depth parentType source selectionSet)) := by
  simpa [GraphQL.Execution.executeRootSelectionSetData] using
    specExecuteCollectedFields_collectFields_response_ready schema resolvers
      variableValues depth parentType source selectionSet

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (variableDefinitions : List VariableDefinition)
    (hselectionSet :
      Validation.selectionSetValid state.window.schema variableDefinitions
        state.window.parentType state.window.selectionSet)
    (hcompatible :
      CollectedGroupsFieldValidationMergeCompatible
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType
          state.window.source state.window.selectionSet))
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_grouped_validation state
  · exact collectFields_pairKeysNodup state.window.schema
      state.window.variableValues state.window.parentType state.window.source
      state.window.selectionSet
  · exact hcompatible
  · exact collectFields_argumentsNodup_of_selectionSetValid state.window.schema
      variableDefinitions state.window.variableValues state.window.parentType
      state.window.parentType state.window.source state.window.selectionSet
      hselectionSet
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_validationCompatible
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (variableDefinitions : List VariableDefinition)
    (hselectionSet :
      Validation.selectionSetValid state.window.schema variableDefinitions
        state.window.parentType state.window.selectionSet)
    (hcompatible :
      CollectedGroupsValidationMergeCompatible
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType
          state.window.source state.window.selectionSet))
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet state
    variableDefinitions hselectionSet
  · exact CollectedGroupsValidationMergeCompatible.fieldCompatible
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType
        state.window.source state.window.selectionSet)
      (collectFields_sameResponseParent state.window.schema
        state.window.variableValues state.window.parentType
        state.window.source state.window.selectionSet)
      hcompatible
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_scopedCompatible
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (variableDefinitions : List VariableDefinition)
    (hselectionSet :
      Validation.selectionSetValid state.window.schema variableDefinitions
        state.window.parentType state.window.selectionSet)
    (hscopedCompatible :
      ScopedFieldsFieldValidationMergeCompatible
        (FieldMerge.collectFields state.window.schema state.window.parentType
          state.window.selectionSet))
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet state
    variableDefinitions hselectionSet
  · exact collectFields_fieldCompatible_of_selectionSetValid_scopedCompatible
      state.window.schema variableDefinitions state.window.variableValues
      state.window.parentType state.window.parentType state.window.source
      state.window.selectionSet hselectionSet hscopedCompatible
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_canMerge_sameScopedParent
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (variableDefinitions : List VariableDefinition)
    (hselectionSet :
      Validation.selectionSetValid state.window.schema variableDefinitions
        state.window.parentType state.window.selectionSet)
    (hmerge :
      FieldMerge.fieldsInSetCanMerge state.window.schema state.window.parentType
        state.window.selectionSet)
    (hsameParent :
      ScopedFieldsSameResponseParent
        (FieldMerge.collectFields state.window.schema state.window.parentType
          state.window.selectionSet))
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_scopedCompatible
    state variableDefinitions hselectionSet
  · exact fieldsInSetCanMerge_scoped_collectFields_fieldCompatible_of_sameParent
      state.window.schema state.window.parentType state.window.selectionSet
      hmerge hsameParent
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_canMerge_runtimeApplies
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (runtimeType : Name)
    (variableDefinitions : List VariableDefinition)
    (hselectionSet :
      Validation.selectionSetValid state.window.schema variableDefinitions
        state.window.parentType state.window.selectionSet)
    (hmerge :
      FieldMerge.fieldsInSetCanMerge state.window.schema state.window.parentType
        state.window.selectionSet)
    (hruntimeApplies :
      ∀ scopedField,
        scopedField ∈
            FieldMerge.collectFields state.window.schema state.window.parentType
              state.window.selectionSet ->
          ScopedFieldRuntimeApplies state.window.schema runtimeType
            scopedField)
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_scopedCompatible
    state variableDefinitions hselectionSet
  · exact
      fieldsInSetCanMerge_scoped_collectFields_fieldCompatible_of_runtimeApplies
        state.window.schema state.window.parentType runtimeType
        state.window.selectionSet hmerge hruntimeApplies
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_canMerge_runtimeScoped
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (runtimeType : Name)
    (variableDefinitions : List VariableDefinition)
    (hselectionSet :
      Validation.selectionSetValid state.window.schema variableDefinitions
        state.window.parentType state.window.selectionSet)
    (hmerge :
      FieldMerge.fieldsInSetCanMerge state.window.schema state.window.parentType
        state.window.selectionSet)
    (hruntimeScoped :
      ExecutableFieldsRuntimeScopedBy state.window.schema runtimeType
        (FieldMerge.collectFields state.window.schema state.window.parentType
          state.window.selectionSet)
        (collectedExecutableFields
          (GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet)))
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet state
    variableDefinitions hselectionSet
  · exact collectFields_fieldCompatible_of_canMerge_runtimeScoped
      state.window.schema state.window.variableValues state.window.parentType
      state.window.parentType runtimeType state.window.source
      state.window.selectionSet hmerge hruntimeScoped
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_canMerge_runtimeScopedBy
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (validParent runtimeType : Name)
    (variableDefinitions : List VariableDefinition)
    (hselectionSet :
      Validation.selectionSetValid state.window.schema variableDefinitions
        validParent state.window.selectionSet)
    (hmerge :
      FieldMerge.fieldsInSetCanMerge state.window.schema validParent
        state.window.selectionSet)
    (hruntimeScoped :
      ExecutableFieldsRuntimeScopedBy state.window.schema runtimeType
        (FieldMerge.collectFields state.window.schema validParent
          state.window.selectionSet)
        (collectedExecutableFields
          (GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet)))
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_grouped_validation state
  · exact collectFields_pairKeysNodup state.window.schema
      state.window.variableValues state.window.parentType state.window.source
      state.window.selectionSet
  · exact collectFields_fieldCompatible_of_canMerge_runtimeScoped
      state.window.schema state.window.variableValues state.window.parentType
      validParent runtimeType state.window.source state.window.selectionSet
      hmerge hruntimeScoped
  · exact collectFields_argumentsNodup_of_selectionSetValid state.window.schema
      variableDefinitions state.window.variableValues state.window.parentType
      validParent state.window.source state.window.selectionSet hselectionSet
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_object_selectionSet_canMerge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (selectionSet : List Selection) (initial : ResponseValue)
    (variableDefinitions : List VariableDefinition)
    (hparentRuntime :
      ScopedParentRuntimeApplies schema runtimeType parentType)
    (hselectionSet :
      Validation.selectionSetValid schema variableDefinitions parentType
        selectionSet)
    (hmerge :
      FieldMerge.fieldsInSetCanMerge schema parentType selectionSet)
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence resolvers
        (.object runtimeType identity)) :
    ExecutionValidFieldSemanticStateInvariant
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := .object runtimeType identity
          selectionSet := selectionSet }
        initial := initial } := by
  apply
    ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_canMerge_runtimeScoped
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := .object runtimeType identity
          selectionSet := selectionSet }
        initial := initial }
      runtimeType variableDefinitions hselectionSet hmerge
  · exact collectFields_runtimeScopedBy_of_selectionSetValid schema
      variableDefinitions variableValues parentType parentType runtimeType
      identity selectionSet hparentRuntime hselectionSet
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_object_selectionSet_canMerge_optional
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (selectionSet : List Selection) (initial : ResponseValue)
    (variableDefinitions : List VariableDefinition)
    (hparentRuntime :
      ScopedParentRuntimeApplies schema runtimeType parentType)
    (hselectionSet :
      Validation.selectionSetValid schema variableDefinitions parentType
        selectionSet)
    (hmerge :
      FieldMerge.fieldsInSetCanMerge schema parentType selectionSet)
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence resolvers
        (.object runtimeType identity)) :
    ExecutionValidFieldSemanticStateInvariant
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := .object runtimeType identity
          selectionSet := selectionSet }
        initial := initial } := by
  apply
    ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_canMerge_runtimeScoped
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := .object runtimeType identity
          selectionSet := selectionSet }
        initial := initial }
      runtimeType variableDefinitions hselectionSet hmerge
  · exact collectFields_runtimeScopedBy_of_selectionSetValid_object schema
      variableDefinitions variableValues parentType parentType runtimeType
      identity selectionSet hparentRuntime hselectionSet
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_object_operation_canMerge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (operation : Operation) (runtimeType : Name)
    (identity : ObjectIdentity) (initial : ResponseValue)
    (hparentRuntime :
      ScopedParentRuntimeApplies schema runtimeType operation.rootType)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence resolvers
        (.object runtimeType identity)) :
    ExecutionValidFieldSemanticStateInvariant
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := operation.rootType
          source := .object runtimeType identity
          selectionSet := operation.selectionSet }
        initial := initial } := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_object_selectionSet_canMerge
    schema resolvers variableValues depth operation.rootType runtimeType
    identity operation.selectionSet initial operation.variableDefinitions
    hparentRuntime
  · exact Validation.operationDefinitionValid_selectionSetValid hvalid
  · exact Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_root_operation_canMerge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (operation : Operation) (runtimeType : Name)
    (identity : ObjectIdentity) (initial : ResponseValue)
    (hroot :
      rootSourceAppliesBool schema operation (.object runtimeType identity) =
        true)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence resolvers
        (.object runtimeType identity)) :
    ExecutionValidFieldSemanticStateInvariant
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := operation.rootType
          source := .object runtimeType identity
          selectionSet := operation.selectionSet }
        initial := initial } := by
  exact ExecutionValidFieldSemanticStateInvariant.of_valid_object_operation_canMerge
    schema resolvers variableValues depth operation runtimeType identity initial
    (ScopedParentRuntimeApplies.of_rootSourceAppliesBool schema operation
      runtimeType identity hroot)
    hvalid hresolvers

theorem ExecutionCollectedFieldInvariant.of_valid_root_operation_canMerge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (operation : Operation) (runtimeType : Name)
    (identity : ObjectIdentity) (initial : ResponseValue)
    (hroot :
      rootSourceAppliesBool schema operation (.object runtimeType identity) =
        true)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence resolvers
        (.object runtimeType identity)) :
    ExecutionCollectedFieldInvariant
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := operation.rootType
          source := .object runtimeType identity
          selectionSet := operation.selectionSet }
        initial := initial } := by
  apply ExecutionCollectedFieldInvariant.of_validFieldSemantic
  exact ExecutionValidFieldSemanticStateInvariant.of_valid_root_operation_canMerge
    schema resolvers variableValues depth operation runtimeType identity
    initial hroot hvalid hresolvers

theorem OperationNoAliasCollision.of_valid_sameScopedParent
    (schema : Schema) (operation : Operation) :
    Validation.operationDefinitionValid schema operation ->
    ScopedFieldsSameResponseParent
      (FieldMerge.collectFields schema operation.rootType
        operation.selectionSet) ->
      OperationNoAliasCollision schema operation := by
  intro hvalid hsameParent
  unfold OperationNoAliasCollision ScopedFieldsNoAliasCollision
  exact fieldsInSetCanMerge_scoped_collectFields_fieldCompatible_of_sameParent
    schema operation.rootType operation.selectionSet
    (Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid)
    hsameParent

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_operation_noAliasCollision
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (operation : Operation) (source : ResolverValue ObjectIdentity)
    (initial : ResponseValue)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hnoAlias : OperationNoAliasCollision schema operation)
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence resolvers source) :
    ExecutionValidFieldSemanticStateInvariant
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := operation.rootType
          source := source
          selectionSet := operation.selectionSet }
        initial := initial } := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_scopedCompatible
    { window :=
      { schema := schema
        resolvers := resolvers
        variableValues := variableValues
        depth := depth
        parentType := operation.rootType
        source := source
        selectionSet := operation.selectionSet }
      initial := initial }
    operation.variableDefinitions
  · exact Validation.operationDefinitionValid_selectionSetValid hvalid
  · exact ScopedFieldsNoAliasCollision.fieldCompatible
      (FieldMerge.collectFields schema operation.rootType operation.selectionSet)
      hnoAlias
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_operation_sameScopedParent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (operation : Operation) (source : ResolverValue ObjectIdentity)
    (initial : ResponseValue)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hsameParent :
      ScopedFieldsSameResponseParent
        (FieldMerge.collectFields schema operation.rootType
          operation.selectionSet))
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence resolvers source) :
    ExecutionValidFieldSemanticStateInvariant
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := operation.rootType
          source := source
          selectionSet := operation.selectionSet }
        initial := initial } := by
  apply
    ExecutionValidFieldSemanticStateInvariant.of_valid_operation_noAliasCollision
      schema resolvers variableValues depth operation source initial hvalid
  · exact OperationNoAliasCollision.of_valid_sameScopedParent schema operation
      hvalid hsameParent
  · exact hresolvers

theorem executeCollectedFields_collectFields_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    PairKeysNodup
      (GraphQL.Execution.executeCollectedFieldsData schema resolvers variableValues
        depth source
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet)) :=
  executeCollectedFields_pairKeysNodup schema resolvers variableValues depth
    source
    (GraphQL.Execution.collectFields schema variableValues parentType source
      selectionSet)
    (collectFields_pairKeysNodup schema variableValues parentType source
      selectionSet)

theorem executeRootSelectionSet_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
      PairKeysNodup
        (GraphQL.Execution.Result.getD []
          (executeRootSelectionSet schema resolvers variableValues depth parentType
            source selectionSet)) := by
    obtain ⟨fields, hfields⟩ :=
      visitSubfields_preserves_object schema resolvers variableValues depth
        parentType source selectionSet []
    have hnodup : PairKeysNodup fields := by
      simpa [hfields] using
        visitSubfields_pairKeysNodup schema resolvers variableValues depth
          parentType source selectionSet [] (by simp [PairKeysNodup])
    unfold executeRootSelectionSet
    cases hstatus :
        (visitSubfields schema resolvers variableValues depth parentType source
          selectionSet (.object [])).snd with
    | error errors =>
        simp [GraphQL.Execution.Result.getD, hstatus, PairKeysNodup]
    | ok status =>
        rcases status with ⟨_unit, errors⟩
        simp [GraphQL.Execution.Result.getD, hstatus, hfields]
        exact hnodup

theorem executeRootSelectionSet_response_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
      ResponseMergeReady
        (.object
          (GraphQL.Execution.Result.getD []
            (executeRootSelectionSet schema resolvers variableValues depth
              parentType source selectionSet))) := by
    obtain ⟨fields, hfields⟩ :=
      visitSubfields_preserves_object schema resolvers variableValues depth
        parentType source selectionSet []
    have hready : ResponseMergeReady (.object fields) := by
      simpa [hfields] using
        visitSubfields_response_ready schema resolvers variableValues depth
          parentType source selectionSet [] ResponseMergeReady_empty_object
    unfold executeRootSelectionSet
    cases hstatus :
        (visitSubfields schema resolvers variableValues depth parentType source
          selectionSet (.object [])).snd with
    | error errors =>
        simp [GraphQL.Execution.Result.getD, hstatus]
        exact ResponseMergeReady_empty_object
    | ok status =>
        rcases status with ⟨_unit, errors⟩
        simp [GraphQL.Execution.Result.getD, hstatus, hfields]
        exact hready

theorem ExecutionWindowEquivalent.ext
    (window : ExecutionWindow ObjectIdentity)
    (hresult :
      window.ungroupedResult = window.specResult) :
    ExecutionWindowEquivalent window := by
  simpa [ExecutionWindowEquivalent, ResponseResultEquivalent] using hresult

theorem ExecutionStateEquivalent.ext
    (state : ExecutionEquivalenceState ObjectIdentity)
    (hresponse : state.ungroupedProjectionResult = state.specProjectionResult) :
    ExecutionStateEquivalent state := by
  simpa [ExecutionStateEquivalent, ResponseResultEquivalent] using hresponse

theorem stateEquivalent_of_executeRootSelectionSet_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
      (hroot :
        executeRootSelectionSet schema resolvers variableValues depth parentType
          source selectionSet =
        GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source selectionSet) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] } := by
    apply ExecutionStateEquivalent.ext
    rw [ExecutionEquivalenceState.ungroupedProjectionResult,
      visitSubfieldsResult_empty_eq_executeRootSelectionSet_object, hroot]
    unfold ExecutionEquivalenceState.specProjectionResult
    unfold GraphQL.Execution.executeRootSelectionSet
    cases hspec :
        GraphQL.Execution.executeCollectedFields schema resolvers variableValues
          depth source
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet) with
    | error errors =>
        simp
    | ok result =>
        rcases result with ⟨fields, errors⟩
        have hnodup : PairKeysNodup fields := by
          have hcollected :=
            executeCollectedFields_collectFields_pairKeysNodup schema resolvers
              variableValues depth parentType source selectionSet
          simpa [GraphQL.Execution.executeCollectedFieldsData,
            GraphQL.Execution.Result.getD, hspec] using hcollected
        have hmerge :
            mergeResponse (.object []) (.object fields) = .object fields :=
          mergeResponse_empty_object_left_of_pairKeysNodup fields hnodup
        simp [hmerge]

theorem stateEquivalent_of_exact_empty_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues depth
        parentType source selectionSet (.object [])) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source selectionSet
    (executeRootSelectionSet_eq_spec_of_exact_empty_group schema resolvers
      variableValues depth parentType source selectionSet hcollect hdirect)

theorem executeRootSelectionSet_eq_spec_of_state_equivalent
    {ObjectIdentity : Type}
    (window : ExecutionWindow ObjectIdentity)
    (hstate :
      ExecutionStateEquivalent
        { window := window, initial := .object [] })
      (hmerge :
        mergeResponse (.object [])
          (.object
          (GraphQL.Execution.executeCollectedFieldsData window.schema
            window.resolvers window.variableValues window.depth window.source
            (GraphQL.Execution.collectFields window.schema window.variableValues
              window.parentType window.source window.selectionSet))) =
        .object
          (GraphQL.Execution.executeCollectedFieldsData window.schema
          window.resolvers window.variableValues window.depth window.source
          (GraphQL.Execution.collectFields window.schema window.variableValues
              window.parentType window.source window.selectionSet))) :
      window.ungroupedResult = window.specResult := by
    have hprojection :
        ExecutionWindow.visitSubfieldsResult window.schema window.resolvers
          window.variableValues window.depth window.parentType window.source
          window.selectionSet (.object []) =
        match
          GraphQL.Execution.executeCollectedFields window.schema
            window.resolvers window.variableValues window.depth window.source
            (GraphQL.Execution.collectFields window.schema
              window.variableValues window.parentType window.source
              window.selectionSet)
        with
        | .error errors => .error errors
        | .ok (fields, errors) =>
            .ok (mergeResponse (.object []) (.object fields), errors) := by
      simpa [ExecutionStateEquivalent, ResponseResultEquivalent,
        ExecutionEquivalenceState.ungroupedProjectionResult,
        ExecutionEquivalenceState.specProjectionResult] using hstate
    rw [visitSubfieldsResult_empty_eq_executeRootSelectionSet_object] at hprojection
    unfold ExecutionWindow.ungroupedResult ExecutionWindow.specResult
    unfold GraphQL.Execution.executeRootSelectionSet
    cases hspec :
        GraphQL.Execution.executeCollectedFields window.schema window.resolvers
          window.variableValues window.depth window.source
          (GraphQL.Execution.collectFields window.schema window.variableValues
            window.parentType window.source window.selectionSet) with
    | error errors =>
        cases hungrouped :
            executeRootSelectionSet window.schema window.resolvers
              window.variableValues window.depth window.parentType
              window.source window.selectionSet with
        | error ungroupedErrors =>
            simpa [hungrouped, hspec] using hprojection
        | ok ungroupedResult =>
            rcases ungroupedResult with ⟨ungroupedFields, ungroupedErrors⟩
            simp [hungrouped, hspec] at hprojection
    | ok result =>
        rcases result with ⟨fields, errors⟩
        have hmergeFields : mergeResponse (.object []) (.object fields) =
            .object fields := by
          have hget :
              GraphQL.Execution.executeCollectedFieldsData window.schema
                window.resolvers window.variableValues window.depth window.source
                (GraphQL.Execution.collectFields window.schema
                  window.variableValues window.parentType window.source
                  window.selectionSet) = fields := by
            simp [GraphQL.Execution.executeCollectedFieldsData,
              GraphQL.Execution.Result.getD, hspec]
          simpa [hget] using hmerge
        cases hungrouped :
            executeRootSelectionSet window.schema window.resolvers
              window.variableValues window.depth window.parentType
              window.source window.selectionSet with
        | error ungroupedErrors =>
            simp [hungrouped, hspec, hmergeFields] at hprojection
        | ok ungroupedResult =>
            rcases ungroupedResult with ⟨ungroupedFields, ungroupedErrors⟩
            have hwrapped :
                (Except.ok (ResponseValue.object ungroupedFields,
                    ungroupedErrors) : Result ResponseValue) =
                  (Except.ok (ResponseValue.object fields, errors) :
                    Result ResponseValue) := by
              simpa [hungrouped, hspec, hmergeFields] using hprojection
            cases hwrapped
            rfl

theorem executeRootSelectionSet_eq_spec_of_state_equivalent_nodup
    {ObjectIdentity : Type}
    (window : ExecutionWindow ObjectIdentity)
    (hstate :
      ExecutionStateEquivalent
        { window := window, initial := .object [] })
    (hnodup :
      PairKeysNodup
        (GraphQL.Execution.executeCollectedFieldsData window.schema
          window.resolvers window.variableValues window.depth window.source
          (GraphQL.Execution.collectFields window.schema window.variableValues
            window.parentType window.source window.selectionSet))) :
      window.ungroupedResult = window.specResult :=
    executeRootSelectionSet_eq_spec_of_state_equivalent window hstate
    (mergeResponse_empty_object_left_of_pairKeysNodup
      (GraphQL.Execution.executeCollectedFieldsData window.schema
        window.resolvers window.variableValues window.depth window.source
        (GraphQL.Execution.collectFields window.schema window.variableValues
          window.parentType window.source window.selectionSet))
      hnodup)

theorem executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
    {ObjectIdentity : Type}
    (window : ExecutionWindow ObjectIdentity)
    (hstate :
      ExecutionStateEquivalent
        { window := window, initial := .object [] }) :
      window.ungroupedResult = window.specResult :=
    executeRootSelectionSet_eq_spec_of_state_equivalent_nodup window hstate
    (executeCollectedFields_collectFields_pairKeysNodup window.schema
      window.resolvers window.variableValues window.depth window.parentType
      window.source window.selectionSet)

theorem executeRootSelectionSet_append_single_field_allowed_eq_combine
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh :
      ∀ fields status,
        visitSubfields schema resolvers variableValues (depth + 1)
          parentType source left (.object []) = (.object fields, status) ->
        responseName ∉ fields.map Prod.fst) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      (left ++ [.field responseName fieldName arguments directives selectionSet]) =
    Result.combine List.append
      (executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source left)
      (executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source
        [.field responseName fieldName arguments directives selectionSet]) := by
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues
      (depth + 1) parentType source left []
  let leftStatus :=
    (visitSubfields schema resolvers variableValues (depth + 1) parentType
      source left (.object [])).snd
  have hleftVisit :
      visitSubfields schema resolvers variableValues (depth + 1) parentType
        source left (.object []) = (.object fields, leftStatus) := by
    exact Prod.ext hfields rfl
  have hfreshFields : responseName ∉ fields.map Prod.fst :=
    hfresh fields leftStatus hleftVisit
  have hrightVisit :
      visitSubfields schema resolvers variableValues (depth + 1)
        parentType source
        [.field responseName fieldName arguments directives selectionSet]
        (.object fields) =
      let fieldResult :=
        executeField schema resolvers variableValues depth source none
          (executableField parentType responseName fieldName arguments
            selectionSet)
      (.object (fields ++ [(responseName, resultValueOrNull fieldResult)]),
        resultStatus fieldResult) :=
    visitSubfields_single_field_allowed_succ_fresh_eq_append schema resolvers
      variableValues depth parentType source responseName fieldName arguments
      directives selectionSet fields hallowed hfreshFields
  have hsingle :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source
        [.field responseName fieldName arguments directives selectionSet] =
      GraphQL.Execution.singleFieldResult responseName
        (executeField schema resolvers variableValues depth source none
          (executableField parentType responseName fieldName arguments
            selectionSet)) :=
    executeRootSelectionSet_single_field_allowed_succ_eq_executeField_empty
      schema resolvers variableValues depth parentType source responseName
      fieldName arguments directives selectionSet hallowed
  have happendVisit :
      visitSubfields schema resolvers variableValues (depth + 1) parentType
        source
        (left ++
          [.field responseName fieldName arguments directives selectionSet])
        (.object []) =
      let fieldResult :=
        executeField schema resolvers variableValues depth source none
          (executableField parentType responseName fieldName arguments
            selectionSet)
      (.object (fields ++ [(responseName, resultValueOrNull fieldResult)]),
        combineVisitStatus leftStatus (resultStatus fieldResult)) := by
    rw [visitSubfields_append_equivalence]
    simp [hleftVisit, hrightVisit]
  have hleftRoot :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source left =
      match leftStatus with
      | .error errors => .error errors
      | .ok (_unit, errors) => .ok (fields, errors) := by
    unfold executeRootSelectionSet
    rw [hleftVisit]
    rfl
  have happendRoot :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source
        (left ++
          [.field responseName fieldName arguments directives selectionSet]) =
      match
        combineVisitStatus leftStatus
          (resultStatus
            (executeField schema resolvers variableValues depth source
              none
              (executableField parentType responseName fieldName arguments
                selectionSet)))
      with
      | .error errors => .error errors
      | .ok (_unit, errors) =>
          .ok
            (fields ++
              [(responseName,
                resultValueOrNull
                  (executeField schema resolvers variableValues depth source
                    none
                    (executableField parentType responseName fieldName
                      arguments selectionSet)))],
              errors) := by
    unfold executeRootSelectionSet
    rw [happendVisit]
    rfl
  rw [happendRoot, hleftRoot, hsingle]
  cases leftStatus with
  | error leftErrors =>
      cases hfield :
          executeField schema resolvers variableValues depth source none
            (executableField parentType responseName fieldName arguments
              selectionSet) <;>
        simp [combineVisitStatus, Result.combine,
          GraphQL.Execution.Result.combine, GraphQL.Execution.singleFieldResult,
          resultStatus, visitOk]
  | ok leftStatusResult =>
      rcases leftStatusResult with ⟨unitValue, leftErrors⟩
      cases unitValue
      cases hfield :
          executeField schema resolvers variableValues depth source none
            (executableField parentType responseName fieldName arguments
              selectionSet) with
      | error fieldErrors =>
          simp [combineVisitStatus, Result.combine,
            GraphQL.Execution.Result.combine, GraphQL.Execution.singleFieldResult,
            resultStatus]
      | ok fieldResult =>
          rcases fieldResult with ⟨response, fieldErrors⟩
          simp [combineVisitStatus, Result.combine,
            GraphQL.Execution.Result.combine, GraphQL.Execution.singleFieldResult,
            resultValueOrNull, resultStatus, visitOk]

theorem stateEquivalent_of_append_single_field_of_disjoint
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth + 1
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hright :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth + 1
            parentType := parentType
            source := source
            selectionSet :=
              [.field responseName fieldName arguments directives selectionSet] }
          initial := .object [] })
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType
          source
          [.field responseName fieldName arguments directives selectionSet]))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth + 1
          parentType := parentType
          source := source
          selectionSet :=
            left ++
              [.field responseName fieldName arguments directives selectionSet] }
        initial := .object [] } := by
  have hleftEq :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source left =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (depth + 1) parentType source left :=
    executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
      { schema := schema
        resolvers := resolvers
        variableValues := variableValues
        depth := depth + 1
        parentType := parentType
        source := source
        selectionSet := left }
      hleft
  have hrightEq :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source
        [.field responseName fieldName arguments directives selectionSet] =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (depth + 1) parentType source
        [.field responseName fieldName arguments directives selectionSet] :=
    executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
      { schema := schema
        resolvers := resolvers
        variableValues := variableValues
        depth := depth + 1
        parentType := parentType
        source := source
        selectionSet :=
          [.field responseName fieldName arguments directives selectionSet] }
      hright
  have hungroupedAppend :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source
        (left ++
          [.field responseName fieldName arguments directives selectionSet]) =
      Result.combine List.append
        (executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source left)
        (executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source
          [.field responseName fieldName arguments directives selectionSet]) :=
    executeRootSelectionSet_append_single_field_allowed_eq_combine schema
      resolvers variableValues depth parentType source left responseName
      fieldName arguments directives selectionSet hallowed
      (responseName_fresh_of_disjoint_single_field_visitSubfields schema
        resolvers variableValues (depth + 1) parentType source left responseName
        fieldName arguments directives selectionSet hdisjoint hallowed)
  have hspecAppend :
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (depth + 1) parentType source
        (left ++
          [.field responseName fieldName arguments directives selectionSet]) =
      Result.combine List.append
        (GraphQL.Execution.executeRootSelectionSet schema resolvers
          variableValues (depth + 1) parentType source left)
        (GraphQL.Execution.executeRootSelectionSet schema resolvers
          variableValues (depth + 1) parentType source
          [.field responseName fieldName arguments directives selectionSet]) :=
    specExecuteRootSelectionSet_append_of_namesDisjoint schema resolvers
      variableValues (depth + 1) parentType source left
      [.field responseName fieldName arguments directives selectionSet]
      hdisjoint
  exact
    stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
      variableValues (depth + 1) parentType source
      (left ++
        [.field responseName fieldName arguments directives selectionSet])
      (by
        calc
          executeRootSelectionSet schema resolvers variableValues (depth + 1)
              parentType source
              (left ++
                [.field responseName fieldName arguments directives
                  selectionSet])
              =
            Result.combine List.append
              (executeRootSelectionSet schema resolvers variableValues
                (depth + 1) parentType source left)
              (executeRootSelectionSet schema resolvers variableValues
                (depth + 1) parentType source
                [.field responseName fieldName arguments directives
                  selectionSet]) := by
              exact hungroupedAppend
          _ =
            Result.combine List.append
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues (depth + 1) parentType source left)
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues (depth + 1) parentType source
                [.field responseName fieldName arguments directives
                  selectionSet]) := by
              rw [hleftEq, hrightEq]
          _ =
            GraphQL.Execution.executeRootSelectionSet schema resolvers
              variableValues (depth + 1) parentType source
              (left ++
                [.field responseName fieldName arguments directives
                  selectionSet]) := by
              exact hspecAppend.symm)

theorem executeRootSelectionSet_append_single_field_blocked_eq_left
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hblocked :
      selectionDirectivesAllowBool variableValues directives = false) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source
      (left ++ [.field responseName fieldName arguments directives selectionSet]) =
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source left := by
  unfold executeRootSelectionSet
  rw [visitSubfields_append_equivalence]
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source left []
  cases hstatus :
      (visitSubfields schema resolvers variableValues depth parentType source
        left (.object [])).snd with
  | error errors =>
      simp [hfields, hstatus, visitSubfields,
        visitSelection_field_directives_blocked schema resolvers
          variableValues depth parentType source responseName fieldName
          arguments directives selectionSet (.object fields) hblocked]
  | ok status =>
      rcases status with ⟨_unit, errors⟩
      simp [hfields, hstatus, visitSubfields,
        visitSelection_field_directives_blocked schema resolvers
          variableValues depth parentType source responseName fieldName
          arguments directives selectionSet (.object fields) hblocked]

theorem specExecuteRootSelectionSet_append_single_field_blocked_eq_left
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hblocked :
      selectionDirectivesAllowBool variableValues directives = false) :
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source
      (left ++ [.field responseName fieldName arguments directives selectionSet]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source left := by
  have hcollect :
      GraphQL.Execution.collectSelection schema variableValues parentType source
        (.field responseName fieldName arguments directives selectionSet) = [] := by
    simp [GraphQL.Execution.collectSelection, hblocked]
  have hcollectAppend :
      GraphQL.Execution.collectFields schema variableValues parentType source
        (left ++ [.field responseName fieldName arguments directives selectionSet]) =
      GraphQL.Execution.collectFields schema variableValues parentType source
        left := by
    rw [GraphQL.NormalForm.collectFields_append]
    simp [GraphQL.Execution.collectFields, hcollect,
      GraphQL.Execution.mergeExecutableGroups]
  simp [GraphQL.Execution.executeRootSelectionSet, hcollectAppend]

theorem executeRootSelectionSet_eq_spec_of_append_single_field_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hblocked :
      selectionDirectivesAllowBool variableValues directives = false) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source
      (left ++ [.field responseName fieldName arguments directives selectionSet]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source
      (left ++ [.field responseName fieldName arguments directives selectionSet]) := by
  calc
    executeRootSelectionSet schema resolvers variableValues depth parentType
        source
        (left ++ [.field responseName fieldName arguments directives selectionSet])
        =
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source left := by
          exact executeRootSelectionSet_append_single_field_blocked_eq_left
            schema resolvers variableValues depth parentType source left
            responseName fieldName arguments directives selectionSet hblocked
    _ =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source left := by
          exact
            executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left }
              hleft
    _ =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source
        (left ++ [.field responseName fieldName arguments directives selectionSet]) := by
          exact
            (specExecuteRootSelectionSet_append_single_field_blocked_eq_left
              schema resolvers variableValues depth parentType source left
              responseName fieldName arguments directives selectionSet
              hblocked).symm

theorem stateEquivalent_of_append_single_field_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hblocked :
      selectionDirectivesAllowBool variableValues directives = false) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet :=
            left ++
              [.field responseName fieldName arguments directives selectionSet] }
        initial := .object [] } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source
    (left ++ [.field responseName fieldName arguments directives selectionSet])
    (executeRootSelectionSet_eq_spec_of_append_single_field_blocked hleft
      hblocked)

theorem executeRootSelectionSet_append_single_selection_noop_eq_left
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection) (selection : Selection)
    (hvisit :
      ∀ fields,
        visitSelection schema resolvers variableValues depth parentType source
          selection (.object fields) = (.object fields, visitOk)) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source (left ++ [selection]) =
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source left := by
  unfold executeRootSelectionSet
  rw [visitSubfields_append_equivalence]
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source left []
  cases hstatus :
      (visitSubfields schema resolvers variableValues depth parentType source
        left (.object [])).snd with
  | error errors =>
      simp [hfields, hstatus, visitSubfields, hvisit fields]
  | ok status =>
      rcases status with ⟨_unit, errors⟩
      simp [hfields, hstatus, visitSubfields, hvisit fields]

theorem specExecuteRootSelectionSet_append_single_selection_noop_eq_left
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection) (selection : Selection)
    (hcollect :
      GraphQL.Execution.collectSelection schema variableValues parentType
        source selection = []) :
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source (left ++ [selection]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source left := by
  have hcollectAppend :
      GraphQL.Execution.collectFields schema variableValues parentType source
        (left ++ [selection]) =
      GraphQL.Execution.collectFields schema variableValues parentType source
        left := by
    rw [GraphQL.NormalForm.collectFields_append]
    simp [GraphQL.Execution.collectFields, hcollect,
      GraphQL.Execution.mergeExecutableGroups]
  simp [GraphQL.Execution.executeRootSelectionSet, hcollectAppend]

theorem executeRootSelectionSet_eq_spec_of_append_single_selection_noop
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} {selection : Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hvisit :
      ∀ fields,
        visitSelection schema resolvers variableValues depth parentType source
          selection (.object fields) = (.object fields, visitOk))
    (hcollect :
      GraphQL.Execution.collectSelection schema variableValues parentType
        source selection = []) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source (left ++ [selection]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source (left ++ [selection]) := by
  calc
    executeRootSelectionSet schema resolvers variableValues depth parentType
        source (left ++ [selection])
        =
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source left := by
          exact executeRootSelectionSet_append_single_selection_noop_eq_left
            schema resolvers variableValues depth parentType source left
            selection hvisit
    _ =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source left := by
          exact
            executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left }
              hleft
    _ =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source (left ++ [selection]) := by
          exact
            (specExecuteRootSelectionSet_append_single_selection_noop_eq_left
              schema resolvers variableValues depth parentType source left
              selection hcollect).symm

theorem stateEquivalent_of_append_single_selection_noop
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} {selection : Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hvisit :
      ∀ fields,
        visitSelection schema resolvers variableValues depth parentType source
          selection (.object fields) = (.object fields, visitOk))
    (hcollect :
      GraphQL.Execution.collectSelection schema variableValues parentType
        source selection = []) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := left ++ [selection] }
        initial := .object [] } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source (left ++ [selection])
    (executeRootSelectionSet_eq_spec_of_append_single_selection_noop hleft
      hvisit hcollect)

theorem stateEquivalent_of_append_single_inline_none_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hblocked :
      selectionDirectivesAllowBool variableValues directives = false) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet :=
            left ++ [.inlineFragment none directives selectionSet] }
        initial := .object [] } :=
  stateEquivalent_of_append_single_selection_noop hleft
    (by
      intro fields
      exact visitSelection_inline_none_directives_blocked schema resolvers
        variableValues depth parentType source directives selectionSet
        (.object fields) hblocked)
    (by
      simp [GraphQL.Execution.collectSelection, hblocked])

theorem stateEquivalent_of_append_single_inline_some_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hblocked :
      selectionDirectivesAllowBool variableValues directives = false) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet :=
            left ++
              [.inlineFragment (some typeCondition) directives selectionSet] }
        initial := .object [] } :=
  stateEquivalent_of_append_single_selection_noop hleft
    (by
      intro fields
      exact visitSelection_inline_some_directives_blocked schema resolvers
        variableValues depth parentType source typeCondition directives
        selectionSet (.object fields) hblocked)
    (by
      simp [GraphQL.Execution.collectSelection, hblocked])

theorem stateEquivalent_of_append_single_inline_some_not_apply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hallowed :
      selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply :
      doesFragmentTypeApplyBool schema parentType source typeCondition =
        false) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet :=
            left ++
              [.inlineFragment (some typeCondition) directives selectionSet] }
        initial := .object [] } :=
  stateEquivalent_of_append_single_selection_noop hleft
    (by
      intro fields
      exact visitSelection_inline_some_type_not_apply schema resolvers
        variableValues depth parentType source typeCondition directives
        selectionSet (.object fields) hallowed hnotApply)
    (by
      simp [GraphQL.Execution.collectSelection, hallowed, hnotApply])

theorem executeRootSelectionSet_append_single_inline_none_allowed_eq_body_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left selectionSet : List Selection)
    (directives : List DirectiveApplication)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source (left ++ [.inlineFragment none directives selectionSet]) =
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source (left ++ selectionSet) := by
  unfold executeRootSelectionSet
  rw [visitSubfields_append_equivalence]
  rw [visitSubfields_append_equivalence]
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source left []
  cases hstatus :
      (visitSubfields schema resolvers variableValues depth parentType source
        left (.object [])).snd with
  | error errors =>
      simp [hfields, hstatus, visitSubfields, visitSelection, hallowed]
  | ok status =>
      rcases status with ⟨_unit, errors⟩
      simp [hfields, hstatus, visitSubfields, visitSelection, hallowed]

theorem specExecuteRootSelectionSet_append_single_inline_none_allowed_eq_body_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left selectionSet : List Selection)
    (directives : List DirectiveApplication)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source
      (left ++ [.inlineFragment none directives selectionSet]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source (left ++ selectionSet) := by
  have hcollectAppend :
      GraphQL.Execution.collectFields schema variableValues parentType source
        (left ++ [.inlineFragment none directives selectionSet]) =
      GraphQL.Execution.collectFields schema variableValues parentType source
        (left ++ selectionSet) := by
    rw [GraphQL.NormalForm.collectFields_append]
    rw [GraphQL.NormalForm.collectFields_append]
    simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
      hallowed, GraphQL.Execution.mergeExecutableGroups]
  simp [GraphQL.Execution.executeRootSelectionSet, hcollectAppend]

theorem executeRootSelectionSet_eq_spec_of_append_single_inline_none_allowed
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left selectionSet : List Selection}
    {directives : List DirectiveApplication}
    (hbody :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left ++ selectionSet }
          initial := .object [] })
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source (left ++ [.inlineFragment none directives selectionSet]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source
      (left ++ [.inlineFragment none directives selectionSet]) := by
  calc
    executeRootSelectionSet schema resolvers variableValues depth parentType
        source (left ++ [.inlineFragment none directives selectionSet])
        =
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source (left ++ selectionSet) := by
          exact executeRootSelectionSet_append_single_inline_none_allowed_eq_body_append
            schema resolvers variableValues depth parentType source left
            selectionSet directives hallowed
    _ =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source (left ++ selectionSet) := by
          exact
            executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left ++ selectionSet }
              hbody
    _ =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source
        (left ++ [.inlineFragment none directives selectionSet]) := by
          exact
            (specExecuteRootSelectionSet_append_single_inline_none_allowed_eq_body_append
              schema resolvers variableValues depth parentType source left
              selectionSet directives hallowed).symm

theorem stateEquivalent_of_append_single_inline_none_allowed
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left selectionSet : List Selection}
    {directives : List DirectiveApplication}
    (hbody :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left ++ selectionSet }
          initial := .object [] })
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet :=
            left ++ [.inlineFragment none directives selectionSet] }
        initial := .object [] } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source
    (left ++ [.inlineFragment none directives selectionSet])
    (executeRootSelectionSet_eq_spec_of_append_single_inline_none_allowed
      hbody hallowed)

theorem executeRootSelectionSet_append_single_inline_some_apply_eq_body_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left selectionSet : List Selection)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (happly :
      doesFragmentTypeApplyBool schema parentType source typeCondition =
        true) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source
      (left ++ [.inlineFragment (some typeCondition) directives selectionSet]) =
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source (left ++ selectionSet) := by
  unfold executeRootSelectionSet
  rw [visitSubfields_append_equivalence]
  rw [visitSubfields_append_equivalence]
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source left []
  cases hstatus :
      (visitSubfields schema resolvers variableValues depth parentType source
        left (.object [])).snd with
  | error errors =>
      simp [hfields, hstatus, visitSubfields, visitSelection, hallowed,
        happly]
  | ok status =>
      rcases status with ⟨_unit, errors⟩
      simp [hfields, hstatus, visitSubfields, visitSelection, hallowed,
        happly]

theorem specExecuteRootSelectionSet_append_single_inline_some_apply_eq_body_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left selectionSet : List Selection)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (happly :
      doesFragmentTypeApplyBool schema parentType source typeCondition =
        true) :
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source
      (left ++ [.inlineFragment (some typeCondition) directives selectionSet]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source (left ++ selectionSet) := by
  have hcollectAppend :
      GraphQL.Execution.collectFields schema variableValues parentType source
        (left ++ [.inlineFragment (some typeCondition) directives selectionSet]) =
      GraphQL.Execution.collectFields schema variableValues parentType source
        (left ++ selectionSet) := by
    rw [GraphQL.NormalForm.collectFields_append]
    rw [GraphQL.NormalForm.collectFields_append]
    simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
      hallowed, happly, GraphQL.Execution.mergeExecutableGroups]
  simp [GraphQL.Execution.executeRootSelectionSet, hcollectAppend]

theorem executeRootSelectionSet_eq_spec_of_append_single_inline_some_apply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left selectionSet : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    (hbody :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left ++ selectionSet }
          initial := .object [] })
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (happly :
      doesFragmentTypeApplyBool schema parentType source typeCondition =
        true) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source
      (left ++ [.inlineFragment (some typeCondition) directives selectionSet]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source
      (left ++ [.inlineFragment (some typeCondition) directives selectionSet]) := by
  calc
    executeRootSelectionSet schema resolvers variableValues depth parentType
        source (left ++ [.inlineFragment (some typeCondition) directives selectionSet])
        =
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source (left ++ selectionSet) := by
          exact executeRootSelectionSet_append_single_inline_some_apply_eq_body_append
            schema resolvers variableValues depth parentType source left
            selectionSet typeCondition directives hallowed happly
    _ =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source (left ++ selectionSet) := by
          exact
            executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left ++ selectionSet }
              hbody
    _ =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source
        (left ++ [.inlineFragment (some typeCondition) directives selectionSet]) := by
          exact
            (specExecuteRootSelectionSet_append_single_inline_some_apply_eq_body_append
              schema resolvers variableValues depth parentType source left
              selectionSet typeCondition directives hallowed happly).symm

theorem stateEquivalent_of_append_single_inline_some_apply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left selectionSet : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    (hbody :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left ++ selectionSet }
          initial := .object [] })
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (happly :
      doesFragmentTypeApplyBool schema parentType source typeCondition =
        true) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet :=
            left ++
              [.inlineFragment (some typeCondition) directives selectionSet] }
        initial := .object [] } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source
    (left ++ [.inlineFragment (some typeCondition) directives selectionSet])
    (executeRootSelectionSet_eq_spec_of_append_single_inline_some_apply
      hbody hallowed happly)

structure AppendAllowedFieldState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection) (childDepth : Nat) : Prop where
  depth_eq : depth = childDepth + 1
  allowed : selectionDirectivesAllowBool variableValues directives = true
  rightEquivalent :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet :=
            [.field responseName fieldName arguments directives selectionSet] }
        initial := .object [] }
  namesDisjoint :
    GraphQL.NormalForm.executableGroupNamesDisjoint
      (GraphQL.Execution.collectFields schema variableValues parentType
        source left)
      (GraphQL.Execution.collectFields schema variableValues parentType source
        [.field responseName fieldName arguments directives selectionSet])

def AppendSelectionState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection) : Selection -> Prop
  | .field responseName fieldName arguments directives selectionSet =>
      selectionDirectivesAllowBool variableValues directives = false ∨
      ∃ childDepth,
        AppendAllowedFieldState schema resolvers variableValues depth parentType
          source left responseName fieldName arguments directives selectionSet
          childDepth
  | .inlineFragment none directives selectionSet =>
      selectionDirectivesAllowBool variableValues directives = false ∨
      selectionDirectivesAllowBool variableValues directives = true ∧
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left ++ selectionSet }
          initial := .object [] }
  | .inlineFragment (some typeCondition) directives selectionSet =>
      selectionDirectivesAllowBool variableValues directives = false ∨
      (selectionDirectivesAllowBool variableValues directives = true ∧
        doesFragmentTypeApplyBool schema parentType source typeCondition =
          false) ∨
      (selectionDirectivesAllowBool variableValues directives = true ∧
        doesFragmentTypeApplyBool schema parentType source typeCondition =
          true ∧
        ExecutionStateEquivalent
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := source
              selectionSet := left ++ selectionSet }
            initial := .object [] })

theorem AppendSelectionState.field_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hblocked :
      selectionDirectivesAllowBool variableValues directives = false) :
    AppendSelectionState schema resolvers variableValues depth parentType
      source left
      (.field responseName fieldName arguments directives selectionSet) := by
  simp [AppendSelectionState, hblocked]

theorem AppendSelectionState.field_allowed
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth childDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hstate :
      AppendAllowedFieldState schema resolvers variableValues depth parentType
        source left responseName fieldName arguments directives selectionSet
        childDepth) :
    AppendSelectionState schema resolvers variableValues depth parentType
      source left
      (.field responseName fieldName arguments directives selectionSet) := by
  simp [AppendSelectionState]
  exact Or.inr ⟨childDepth, hstate⟩

theorem AppendSelectionState.inline_none_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hblocked :
      selectionDirectivesAllowBool variableValues directives = false) :
    AppendSelectionState schema resolvers variableValues depth parentType
      source left (.inlineFragment none directives selectionSet) := by
  simp [AppendSelectionState, hblocked]

theorem AppendSelectionState.inline_none_allowed
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hbody :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left ++ selectionSet }
          initial := .object [] }) :
    AppendSelectionState schema resolvers variableValues depth parentType
      source left (.inlineFragment none directives selectionSet) := by
  simp [AppendSelectionState, hallowed, hbody]

theorem AppendSelectionState.inline_some_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} {typeCondition : Name}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hblocked :
      selectionDirectivesAllowBool variableValues directives = false) :
    AppendSelectionState schema resolvers variableValues depth parentType
      source left
      (.inlineFragment (some typeCondition) directives selectionSet) := by
  simp [AppendSelectionState, hblocked]

theorem AppendSelectionState.inline_some_not_apply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} {typeCondition : Name}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply :
      doesFragmentTypeApplyBool schema parentType source typeCondition =
        false) :
    AppendSelectionState schema resolvers variableValues depth parentType
      source left
      (.inlineFragment (some typeCondition) directives selectionSet) := by
  simp [AppendSelectionState, hallowed, hnotApply]

theorem AppendSelectionState.inline_some_apply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} {typeCondition : Name}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (happly :
      doesFragmentTypeApplyBool schema parentType source typeCondition =
        true)
    (hbody :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left ++ selectionSet }
          initial := .object [] }) :
    AppendSelectionState schema resolvers variableValues depth parentType
      source left
      (.inlineFragment (some typeCondition) directives selectionSet) := by
  simp [AppendSelectionState, hallowed, happly, hbody]

theorem stateEquivalent_of_append_single_selection_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} (selection : Selection)
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hselection :
      AppendSelectionState schema resolvers variableValues depth parentType
        source left selection) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := left ++ [selection] }
        initial := .object [] } := by
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      simp [AppendSelectionState] at hselection
      rcases hselection with hblocked | hrest
      · exact stateEquivalent_of_append_single_field_blocked hleft hblocked
      · rcases hrest with ⟨childDepth, hstep⟩
        cases hstep.depth_eq
        exact stateEquivalent_of_append_single_field_of_disjoint hleft
          hstep.rightEquivalent hstep.namesDisjoint hstep.allowed
  | inlineFragment typeCondition directives selectionSet =>
      cases typeCondition with
      | none =>
          simp [AppendSelectionState] at hselection
          rcases hselection with hblocked | hallowedBody
          · exact stateEquivalent_of_append_single_inline_none_blocked hleft
              hblocked
          · rcases hallowedBody with ⟨hallowed, hbody⟩
            exact stateEquivalent_of_append_single_inline_none_allowed hbody
              hallowed
      | some typeCondition =>
          simp [AppendSelectionState] at hselection
          rcases hselection with hblocked | hnotApplyStep | happlyStep
          · exact stateEquivalent_of_append_single_inline_some_blocked hleft
              hblocked
          · rcases hnotApplyStep with ⟨hallowed, hnotApply⟩
            exact stateEquivalent_of_append_single_inline_some_not_apply hleft
              hallowed hnotApply
          · rcases happlyStep with ⟨hallowed, happly, hbody⟩
            exact stateEquivalent_of_append_single_inline_some_apply hbody
              hallowed happly

def AppendSelectionSetState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    List Selection -> List Selection -> Prop
  | _left, [] => True
  | left, selection :: rest =>
      AppendSelectionState schema resolvers variableValues depth parentType
        source left selection ∧
      AppendSelectionSetState schema resolvers variableValues depth parentType
        source (left ++ [selection]) rest

theorem AppendSelectionSetState.nil
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} :
    AppendSelectionSetState schema resolvers variableValues depth parentType
      source left [] := by
  simp [AppendSelectionSetState]

theorem AppendSelectionSetState.cons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} {selection : Selection} {rest : List Selection}
    (hselection :
      AppendSelectionState schema resolvers variableValues depth parentType
        source left selection)
    (hrest :
      AppendSelectionSetState schema resolvers variableValues depth parentType
        source (left ++ [selection]) rest) :
    AppendSelectionSetState schema resolvers variableValues depth parentType
      source left (selection :: rest) := by
  exact ⟨hselection, hrest⟩

def AppendSelectionSetPrefixState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left selectionSet : List Selection) : Prop :=
  ∀ prefixSelections selection suffix,
    selectionSet = prefixSelections ++ selection :: suffix ->
      AppendSelectionState schema resolvers variableValues depth parentType
        source (left ++ prefixSelections) selection

theorem AppendSelectionSetPrefixState.nil
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} :
    AppendSelectionSetPrefixState schema resolvers variableValues depth
      parentType source left [] := by
  intro prefixSelections selection suffix hselectionSet
  have hlength := congrArg List.length hselectionSet
  simp at hlength

theorem AppendSelectionSetPrefixState.singleton
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} {selection : Selection}
    (hselection :
      AppendSelectionState schema resolvers variableValues depth parentType
        source left selection) :
    AppendSelectionSetPrefixState schema resolvers variableValues depth
      parentType source left [selection] := by
  intro prefixSelections nextSelection suffix hselectionSet
  cases prefixSelections with
  | nil =>
      simp at hselectionSet
      rcases hselectionSet with ⟨rfl, rfl⟩
      simpa using hselection
  | cons _head _tail =>
      have hlength := congrArg List.length hselectionSet
      simp at hlength

theorem AppendSelectionSetPrefixState.cons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} {selection : Selection}
    {rest : List Selection}
    (hselection :
      AppendSelectionState schema resolvers variableValues depth parentType
        source left selection)
    (hrest :
      AppendSelectionSetPrefixState schema resolvers variableValues depth
        parentType source (left ++ [selection]) rest) :
    AppendSelectionSetPrefixState schema resolvers variableValues depth
      parentType source left (selection :: rest) := by
  intro prefixSelections nextSelection suffix hselectionSet
  cases prefixSelections with
  | nil =>
      simp at hselectionSet
      rcases hselectionSet with ⟨rfl, _hrest⟩
      simpa using hselection
  | cons head tail =>
      simp at hselectionSet
      rcases hselectionSet with ⟨rfl, hrestSet⟩
      have hstep := hrest tail nextSelection suffix hrestSet
      simpa [List.append_assoc] using hstep

theorem AppendSelectionSetState.of_prefix_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity} :
    ∀ (left selectionSet : List Selection),
      AppendSelectionSetPrefixState schema resolvers variableValues depth
        parentType source left selectionSet ->
      AppendSelectionSetState schema resolvers variableValues depth parentType
        source left selectionSet
  | _left, [], _hstate => by
      exact AppendSelectionSetState.nil
  | left, selection :: rest, hstate => by
      apply AppendSelectionSetState.cons
      · simpa using hstate [] selection rest rfl
      · apply AppendSelectionSetState.of_prefix_state
        intro prefixSelections tailSelection suffix htail
        have hselectionSet :
            selection :: rest =
              (selection :: prefixSelections) ++ tailSelection :: suffix := by
          simp [htail]
        have hstep :=
          hstate (selection :: prefixSelections) tailSelection suffix hselectionSet
        simpa [List.append_assoc] using hstep

theorem AppendSelectionSetState.append
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity} :
    ∀ (left middle right : List Selection),
      AppendSelectionSetState schema resolvers variableValues depth parentType
        source left middle ->
      AppendSelectionSetState schema resolvers variableValues depth parentType
        source (left ++ middle) right ->
      AppendSelectionSetState schema resolvers variableValues depth parentType
        source left (middle ++ right)
  | _left, [], right, _hmiddle, hright => by
      simpa using hright
  | left, selection :: rest, right, hmiddle, hright => by
      rcases hmiddle with ⟨hselection, hrest⟩
      apply AppendSelectionSetState.cons hselection
      apply AppendSelectionSetState.append (left ++ [selection]) rest right hrest
      simpa [List.append_assoc] using hright

theorem stateEquivalent_of_append_selectionSet_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity} :
    ∀ (left right : List Selection),
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] } ->
      AppendSelectionSetState schema resolvers variableValues depth parentType
        source left right ->
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left ++ right }
          initial := .object [] }
  | left, [], hleft, _hstate => by
      simpa using hleft
  | left, selection :: rest, hleft, hstate => by
      simp [AppendSelectionSetState] at hstate
      rcases hstate with ⟨hselection, hrest⟩
      have hfirst :
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left ++ [selection] }
              initial := .object [] } :=
        stateEquivalent_of_append_single_selection_state selection hleft
          hselection
      have htail :=
        stateEquivalent_of_append_selectionSet_state
          (left ++ [selection]) rest hfirst hrest
      simpa [List.append_assoc] using htail

theorem stateEquivalent_of_selectionSet_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (hstate :
      AppendSelectionSetState schema resolvers variableValues depth parentType
        source [] selectionSet) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] } := by
  simpa using
    stateEquivalent_of_append_selectionSet_state
      ([] : List Selection) selectionSet
      (emptySelectionStateEquivalent schema resolvers variableValues depth
        parentType source (.object []))
      hstate

theorem stateEquivalent_of_selectionSet_prefix_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (hstate :
      AppendSelectionSetPrefixState schema resolvers variableValues depth
        parentType source [] selectionSet) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] } :=
  stateEquivalent_of_selectionSet_state
    (AppendSelectionSetState.of_prefix_state [] selectionSet hstate)

theorem executeRootSelectionSet_eq_spec_of_selectionSet_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (hstate :
      AppendSelectionSetState schema resolvers variableValues depth parentType
        source [] selectionSet) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
    { schema := schema
      resolvers := resolvers
      variableValues := variableValues
      depth := depth
      parentType := parentType
      source := source
      selectionSet := selectionSet }
    (stateEquivalent_of_selectionSet_state hstate)

theorem executeRootSelectionSet_eq_spec_of_selectionSet_prefix_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (hstate :
      AppendSelectionSetPrefixState schema resolvers variableValues depth
        parentType source [] selectionSet) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_selectionSet_state
    (AppendSelectionSetState.of_prefix_state [] selectionSet hstate)

theorem executeQueryAtDepth_eq_spec_of_root_fields_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hfields :
      executeRootSelectionSet schema resolvers variableValues depth
        operation.rootType source operation.selectionSet =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth operation.rootType source operation.selectionSet) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues operation
      depth source := by
  rw [executeQueryAtDepth, GraphQL.Execution.executeQueryAtDepth, hroot,
    hfields]
  rfl

theorem executeQueryAtDepth_eq_spec_of_root_false
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = false) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues operation
      depth source := by
  rw [executeQueryAtDepth, GraphQL.Execution.executeQueryAtDepth, hroot]
  simp

theorem executeQueryAtDepth_eq_spec_of_state_equivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hstate :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := operation.rootType
            source := source
            selectionSet := operation.selectionSet }
          initial := .object [] }) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues operation
      depth source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation depth source hroot
  exact
    executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
      { schema := schema
        resolvers := resolvers
        variableValues := variableValues
        depth := depth
        parentType := operation.rootType
        source := source
        selectionSet := operation.selectionSet }
      hstate

theorem executeQueryAtDepth_eq_spec_of_selectionSet_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hstate :
      AppendSelectionSetState schema resolvers variableValues depth
        operation.rootType source [] operation.selectionSet) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues operation
      depth source :=
  executeQueryAtDepth_eq_spec_of_state_equivalent schema resolvers
    variableValues operation depth source hroot
    (stateEquivalent_of_selectionSet_state hstate)

theorem executeQueryAtDepth_eq_spec_of_selectionSet_prefix_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hstate :
      AppendSelectionSetPrefixState schema resolvers variableValues depth
        operation.rootType source [] operation.selectionSet) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues operation
      depth source :=
  executeQueryAtDepth_eq_spec_of_selectionSet_state schema resolvers
    variableValues operation depth source hroot
    (AppendSelectionSetState.of_prefix_state [] operation.selectionSet hstate)

theorem executeQueryAtDepth_eq_spec_of_flattened_collectFields_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hflat :
      executeRootSelectionSet schema resolvers variableValues depth
        operation.rootType source operation.selectionSet =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth operation.rootType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues
              operation.rootType source operation.selectionSet)))) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues operation
      depth source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation depth source hroot
  exact executeRootSelectionSet_eq_spec_of_flattened_collectFields_eq schema
    resolvers variableValues depth operation.rootType source
    operation.selectionSet hflat

theorem executeQueryAtDepth_eq_spec_of_flat_predicates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues depth
        operation.rootType source operation.selectionSet (.object []))
    (hflatSpec :
      ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues depth
        operation.rootType source
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues
            operation.rootType source operation.selectionSet))) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues operation
      depth source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation depth source hroot
  exact executeRootSelectionSet_eq_spec_of_flatCollects_and_flatSpecEquivalent
    schema resolvers variableValues depth operation.rootType source
    operation.selectionSet hdirect hflatSpec

theorem executeQueryAtDepth_eq_spec_of_group_flat_predicates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues depth
        operation.rootType source operation.selectionSet (.object []))
    (hgroups :
      ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues depth
        operation.rootType source
        (GraphQL.Execution.collectFields schema variableValues operation.rootType
          source operation.selectionSet)) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues operation
      depth source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation depth source hroot
  exact
    executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
      schema resolvers variableValues depth operation.rootType source
      operation.selectionSet hdirect hgroups

theorem executeQueryAtDepth_eq_spec_of_exact_empty_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues depth
        operation.rootType source operation.selectionSet (.object [])) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues operation
      depth source := by
  apply executeQueryAtDepth_eq_spec_of_state_equivalent schema resolvers
    variableValues operation depth source hroot
  exact stateEquivalent_of_exact_empty_group schema resolvers variableValues
    depth operation.rootType source operation.selectionSet hcollect hdirect

theorem executeQuery_eq_spec_of_root_fields_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hfields :
      executeRootSelectionSet schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source operation.selectionSet =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source operation.selectionSet) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers variableValues
    operation (GraphQL.Execution.executeQueryDepthBound operation) source hroot
    hfields

theorem executeQuery_eq_spec_of_state_equivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hstate :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := GraphQL.Execution.executeQueryDepthBound operation
            parentType := operation.rootType
            source := source
            selectionSet := operation.selectionSet }
          initial := .object [] }) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryAtDepth_eq_spec_of_state_equivalent schema resolvers
    variableValues operation (GraphQL.Execution.executeQueryDepthBound operation)
    source hroot hstate

theorem executeQuery_eq_spec_of_selectionSet_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hstate :
      AppendSelectionSetState schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source [] operation.selectionSet) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryAtDepth_eq_spec_of_selectionSet_state schema resolvers
    variableValues operation (GraphQL.Execution.executeQueryDepthBound operation)
    source hroot hstate

theorem executeQuery_eq_spec_of_selectionSet_prefix_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hstate :
      AppendSelectionSetPrefixState schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source [] operation.selectionSet) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact
    executeQueryAtDepth_eq_spec_of_selectionSet_prefix_state schema resolvers
      variableValues operation (GraphQL.Execution.executeQueryDepthBound operation)
      source hroot hstate

theorem executeQuery_eq_spec_of_flattened_collectFields_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hflat :
      executeRootSelectionSet schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source operation.selectionSet =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues
              operation.rootType source operation.selectionSet)))) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryAtDepth_eq_spec_of_flattened_collectFields_eq schema
    resolvers variableValues operation
    (GraphQL.Execution.executeQueryDepthBound operation) source hroot hflat

theorem executeQuery_eq_spec_of_flat_predicates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source operation.selectionSet (.object []))
    (hflatSpec :
      ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues
            operation.rootType source operation.selectionSet))) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryAtDepth_eq_spec_of_flat_predicates schema resolvers
    variableValues operation (GraphQL.Execution.executeQueryDepthBound operation)
    source hroot hdirect hflatSpec

theorem executeQuery_eq_spec_of_group_flat_predicates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source operation.selectionSet (.object []))
    (hgroups :
      ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source
        (GraphQL.Execution.collectFields schema variableValues operation.rootType
          source operation.selectionSet)) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryAtDepth_eq_spec_of_group_flat_predicates schema resolvers
    variableValues operation (GraphQL.Execution.executeQueryDepthBound operation)
    source hroot hdirect hgroups

theorem executeQuery_eq_spec_of_exact_empty_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source operation.selectionSet (.object [])) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryAtDepth_eq_spec_of_exact_empty_group schema resolvers
    variableValues operation (GraphQL.Execution.executeQueryDepthBound operation)
    source hroot hcollect hdirect

theorem executeRootSelectionSet_single_field_succ_eq_spec_of_completeValue
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hcomplete :
      GraphQL.Execution.singleFieldResult responseName
        (executeField schema resolvers variableValues depth source none
          (executableField parentType responseName fieldName arguments
            selectionSet)) =
      GraphQL.Execution.executeField schema resolvers variableValues (depth + 1)
        source responseName
        [executableField parentType responseName fieldName arguments
          selectionSet]) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      [.field responseName fieldName arguments directives selectionSet] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet] := by
  have hleft :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source
          [.field responseName fieldName arguments directives selectionSet]
        =
      GraphQL.Execution.singleFieldResult responseName
        (executeField schema resolvers variableValues depth source none
          (executableField parentType responseName fieldName arguments
            selectionSet)) := by
    cases hfield :
        executeField schema resolvers variableValues depth source none
          (executableField parentType responseName fieldName arguments
            selectionSet) <;>
      simp only [executableField] at hfield <;>
      simp [executeRootSelectionSet, visitSubfields, visitSelection, hallowed,
        executableField, GraphQL.Execution.singleFieldResult,
        mergeResponseFieldResult, mergeResponseFieldIntoObject,
        mergeResponseField, responseObjectField?, lookupResponseField?, resultValueOrNull,
        resultStatus, visitOk, combineVisitStatus, Result.combine,
        GraphQL.Execution.Result.combine, hfield]
  have hright :
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source
          [.field responseName fieldName arguments directives selectionSet]
        =
      GraphQL.Execution.executeField schema resolvers variableValues (depth + 1)
        source responseName
        [executableField parentType responseName fieldName arguments
          selectionSet] := by
    cases hspec :
        GraphQL.Execution.executeField schema resolvers variableValues
          (depth + 1) source responseName
          [executableField parentType responseName fieldName arguments
            selectionSet] <;>
      simp only [executableField] at hspec <;>
      simp [GraphQL.Execution.executeRootSelectionSet,
        GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups,
        GraphQL.Execution.executeCollectedFields,
        Result.combine,
        GraphQL.Execution.Result.combine, hallowed, hspec]
  exact hleft.trans (hcomplete.trans hright.symm)

theorem completeValue_object_group_eq_spec_of_merged_child_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (fields : List ExecutableField)
    (hchild :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType identity
            selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields }
          initial := .object [] }) :
    completeValue schema resolvers variableValues (childDepth + 1)
      parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
      (.object runtimeType identity) none =
    GraphQL.Execution.completeValue schema resolvers variableValues
      (childDepth + 1) parentType fields (.object runtimeType identity) := by
  cases hincludes :
      schema.typeIncludesObjectBool parentType runtimeType with
  | false =>
      simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
        GraphQL.Execution.completeValue, hincludes]
  | true =>
      unfold ExecutionStateEquivalent ResponseResultEquivalent at hchild
      unfold ExecutionEquivalenceState.ungroupedProjectionResult at hchild
      unfold ExecutionEquivalenceState.specProjectionResult at hchild
      unfold ExecutionWindow.visitSubfieldsResult at hchild
      simp only [hincludes, GraphQL.Algorithms.ExecutionUngrouped.completeValue,
        GraphQL.Execution.completeValue, reuseOrCreateObject?]
      rw [GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
      cases hvisit :
          visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet fields) (.object []) with
      | mk output status =>
          cases hcompleted :
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues childDepth (.object runtimeType identity)
                (GraphQL.Execution.collectFields schema variableValues runtimeType
                  (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet fields)) with
          | error errors =>
              cases status with
              | error visitErrors =>
                  simpa [hvisit, hcompleted, reuseOrCreateObject?,
                    catchVisitBubbleAsNull,
                    GraphQL.Execution.catchBubbleAsNull] using hchild
              | ok statusResult =>
                  rcases statusResult with ⟨unitValue, visitErrors⟩
                  cases unitValue
                  simp [hvisit, hcompleted] at hchild
          | ok completed =>
              rcases completed with ⟨completedFields, completedErrors⟩
              have hnodup : PairKeysNodup completedFields := by
                have hcollected :=
                  executeCollectedFields_collectFields_pairKeysNodup schema
                    resolvers variableValues childDepth runtimeType
                    (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet fields)
                simpa [GraphQL.Execution.executeCollectedFieldsData,
                  GraphQL.Execution.Result.getD, hcompleted] using hcollected
              have hmerge :
                  mergeResponse (.object []) (.object completedFields) =
                    .object completedFields :=
                mergeResponse_empty_object_left_of_pairKeysNodup completedFields
                  hnodup
              cases status with
              | error visitErrors =>
                  simp [hvisit, hcompleted, hmerge] at hchild
              | ok statusResult =>
                  rcases statusResult with ⟨unitValue, visitErrors⟩
                  cases unitValue
                  simpa [hvisit, hcompleted, hmerge, reuseOrCreateObject?,
                    catchVisitBubbleAsNull,
                    GraphQL.Execution.catchBubbleAsNull] using hchild

theorem completeValue_object_group_eq_spec_of_guarded_merged_child_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (fields : List ExecutableField)
    (hchild :
      schema.typeIncludesObjectBool parentType runtimeType = true ->
        ExecutionStateEquivalent
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := childDepth
              parentType := runtimeType
              source := .object runtimeType identity
              selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields }
            initial := .object [] }) :
    completeValue schema resolvers variableValues (childDepth + 1)
      parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
      (.object runtimeType identity) none =
    GraphQL.Execution.completeValue schema resolvers variableValues
      (childDepth + 1) parentType fields (.object runtimeType identity) := by
  cases hincludes :
      schema.typeIncludesObjectBool parentType runtimeType with
  | false =>
      simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
        GraphQL.Execution.completeValue, hincludes]
  | true =>
      exact
        completeValue_object_group_eq_spec_of_merged_child_state schema
          resolvers variableValues childDepth parentType runtimeType identity
          fields (hchild hincludes)

theorem completeValueList_object_group_eq_spec_of_merged_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType : Name) (fields : List ExecutableField) :
    ∀ (objects : List (Name × ObjectIdentity)),
      (∀ object, object ∈ objects ->
        ExecutionStateEquivalent
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := childDepth
              parentType := object.fst
              source := .object object.fst object.snd
              selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields }
            initial := .object [] }) ->
      completeValueList schema resolvers variableValues (childDepth + 1)
        parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
        (objects.map
          (fun object => (.object object.fst object.snd : ResolverValue ObjectIdentity)))
        [] =
      GraphQL.Execution.completeValueList schema resolvers variableValues
        (childDepth + 1) parentType fields
        (objects.map
          (fun object => (.object object.fst object.snd : ResolverValue ObjectIdentity)))
  | [], _hchildren => by
      simp [completeValueList, GraphQL.Execution.completeValueList]
  | object :: rest, hchildren => by
      have hhead :
          completeValue schema resolvers variableValues (childDepth + 1)
            parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
            (.object object.fst object.snd) none =
          GraphQL.Execution.completeValue schema resolvers variableValues
            (childDepth + 1) parentType fields
            (.object object.fst object.snd) :=
        completeValue_object_group_eq_spec_of_merged_child_state schema
          resolvers variableValues childDepth parentType object.fst object.snd
          fields (hchildren object (by simp))
      have hrest :
          completeValueList schema resolvers variableValues (childDepth + 1)
            parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
            (rest.map
              (fun object =>
                (.object object.fst object.snd : ResolverValue ObjectIdentity)))
            [] =
          GraphQL.Execution.completeValueList schema resolvers variableValues
            (childDepth + 1) parentType fields
            (rest.map
              (fun object =>
                (.object object.fst object.snd : ResolverValue ObjectIdentity))) :=
        completeValueList_object_group_eq_spec_of_merged_child_states schema
          resolvers variableValues childDepth parentType fields rest
          (by
            intro restObject hmem
            exact hchildren restObject (by simp [hmem]))
      simp [List.map_cons, completeValueList,
        GraphQL.Execution.completeValueList, hhead, hrest, Result.combine,
        GraphQL.Execution.Result.combine]

theorem completeValueList_object_group_eq_spec_of_guarded_merged_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType : Name) (fields : List ExecutableField) :
    ∀ (objects : List (Name × ObjectIdentity)),
      (∀ object, object ∈ objects ->
        schema.typeIncludesObjectBool parentType object.fst = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := object.fst
                source := .object object.fst object.snd
                selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields }
              initial := .object [] }) ->
      completeValueList schema resolvers variableValues (childDepth + 1)
        parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
        (objects.map
          (fun object => (.object object.fst object.snd : ResolverValue ObjectIdentity)))
        [] =
      GraphQL.Execution.completeValueList schema resolvers variableValues
        (childDepth + 1) parentType fields
        (objects.map
          (fun object => (.object object.fst object.snd : ResolverValue ObjectIdentity)))
  | [], _hchildren => by
      simp [completeValueList, GraphQL.Execution.completeValueList]
  | object :: rest, hchildren => by
      have hhead :
          completeValue schema resolvers variableValues (childDepth + 1)
            parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
            (.object object.fst object.snd) none =
          GraphQL.Execution.completeValue schema resolvers variableValues
            (childDepth + 1) parentType fields
            (.object object.fst object.snd) :=
        completeValue_object_group_eq_spec_of_guarded_merged_child_state schema
          resolvers variableValues childDepth parentType object.fst object.snd
          fields
          (by
            intro hincludes
            exact hchildren object (by simp) hincludes)
      have hrest :
          completeValueList schema resolvers variableValues (childDepth + 1)
            parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
            (rest.map
              (fun object =>
                (.object object.fst object.snd : ResolverValue ObjectIdentity)))
            [] =
          GraphQL.Execution.completeValueList schema resolvers variableValues
            (childDepth + 1) parentType fields
            (rest.map
              (fun object =>
                (.object object.fst object.snd : ResolverValue ObjectIdentity))) :=
        completeValueList_object_group_eq_spec_of_guarded_merged_child_states
          schema resolvers variableValues childDepth parentType fields rest
          (by
            intro restObject hmem hincludes
            exact hchildren restObject (by simp [hmem]) hincludes)
      simp [List.map_cons, completeValueList,
        GraphQL.Execution.completeValueList, hhead, hrest, Result.combine,
        GraphQL.Execution.Result.combine]

theorem completeValue_object_list_group_eq_spec_of_merged_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType : Name) (fields : List ExecutableField)
    (objects : List (Name × ObjectIdentity))
    (_hchildren :
      ∀ object, object ∈ objects ->
        ExecutionStateEquivalent
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := childDepth
              parentType := object.fst
              source := .object object.fst object.snd
              selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields }
            initial := .object [] }) :
    completeValue schema resolvers variableValues (childDepth + 2)
      parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
      (.list
        (objects.map
          (fun object => (.object object.fst object.snd : ResolverValue ObjectIdentity))))
      none =
    GraphQL.Execution.completeValue schema resolvers variableValues
      (childDepth + 2) parentType fields
      (.list
        (objects.map
          (fun object => (.object object.fst object.snd : ResolverValue ObjectIdentity)))) := by
  simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
    GraphQL.Execution.completeValue]

theorem completeValue_object_list_group_eq_spec_of_guarded_merged_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType : Name) (fields : List ExecutableField)
    (objects : List (Name × ObjectIdentity))
    (_hchildren :
      ∀ object, object ∈ objects ->
        schema.typeIncludesObjectBool parentType object.fst = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := object.fst
                source := .object object.fst object.snd
                selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields }
              initial := .object [] }) :
    completeValue schema resolvers variableValues (childDepth + 2)
      parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
      (.list
        (objects.map
          (fun object => (.object object.fst object.snd : ResolverValue ObjectIdentity))))
      none =
    GraphQL.Execution.completeValue schema resolvers variableValues
      (childDepth + 2) parentType fields
      (.list
        (objects.map
          (fun object => (.object object.fst object.snd : ResolverValue ObjectIdentity)))) := by
  simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
    GraphQL.Execution.completeValue]

theorem completeValue_group_eq_spec_of_merged_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (fields : List ExecutableField) :
    ∀ (depth : Nat) (parentType : Name) (value : ResolverValue ObjectIdentity),
      (∀ childDepth runtimeType (identity : ObjectIdentity),
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields }
              initial := .object [] }) ->
        completeValue schema resolvers variableValues depth parentType
          (GraphQL.Execution.mergedFieldSelectionSet fields) value none =
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          parentType fields value := by
  intro depth parentType value hchildren
  cases depth with
  | zero =>
      cases value <;>
        simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
          GraphQL.Execution.completeValue, outOfFuel]
  | succ childDepth =>
      cases value with
      | null =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue]
      | scalar value =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue]
      | object runtimeType identity =>
          exact
            completeValue_object_group_eq_spec_of_merged_child_state schema
              resolvers variableValues childDepth parentType runtimeType
              identity fields
              (hchildren childDepth runtimeType identity
                (Nat.lt_succ_self childDepth))
      | list values =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue]

theorem completeValue_group_eq_spec_of_guarded_merged_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (fields : List ExecutableField) :
    ∀ (depth : Nat) (parentType : Name) (value : ResolverValue ObjectIdentity),
      (∀ childDepth runtimeType (identity : ObjectIdentity),
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
                selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields }
              initial := .object [] }) ->
        completeValue schema resolvers variableValues depth parentType
          (GraphQL.Execution.mergedFieldSelectionSet fields) value none =
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          parentType fields value := by
  intro depth parentType value hchildren
  cases depth with
  | zero =>
      cases value <;>
        simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
          GraphQL.Execution.completeValue, outOfFuel]
  | succ childDepth =>
      cases value with
      | null =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue]
      | scalar value =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue]
      | object runtimeType identity =>
          exact
            completeValue_object_group_eq_spec_of_guarded_merged_child_state
              schema resolvers variableValues childDepth parentType runtimeType
              identity fields
              (by
                intro hincludes
                exact hchildren childDepth runtimeType identity
                  (Nat.lt_succ_self childDepth) hincludes)
      | list values =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue]

theorem completeValue_group_eq_spec_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (fields : List ExecutableField) :
    ∀ (depth : Nat) (parentType : Name) (value : ResolverValue ObjectIdentity),
      (∀ childDepth runtimeType (identity : ObjectIdentity),
        childDepth < depth ->
        ValueContainsObject value runtimeType identity ->
        schema.typeIncludesObjectBool parentType runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields }
              initial := .object [] }) ->
        completeValue schema resolvers variableValues depth parentType
          (GraphQL.Execution.mergedFieldSelectionSet fields) value none =
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          parentType fields value := by
  intro depth parentType value hchildren
  cases depth with
  | zero =>
      cases value <;>
        simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
          GraphQL.Execution.completeValue, outOfFuel]
  | succ childDepth =>
      cases value with
      | null =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue]
      | scalar value =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue]
      | object runtimeType identity =>
          exact
            completeValue_object_group_eq_spec_of_guarded_merged_child_state
              schema resolvers variableValues childDepth parentType runtimeType
              identity fields
              (by
                intro hincludes
                exact hchildren childDepth runtimeType identity
                  (Nat.lt_succ_self childDepth)
                  ValueContainsObject.here hincludes)
      | list values =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue]

theorem completeValue_single_field_eq_spec_of_guarded_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (field : ExecutableField) :
    ∀ (fieldType : TypeRef) (depth : Nat)
      (value : ResolverValue ObjectIdentity),
      (∀ childDepth runtimeType (identity : ObjectIdentity),
        childDepth < depth ->
        schema.typeIncludesObjectBool fieldType.namedType runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] }) ->
        completeValue schema resolvers variableValues depth fieldType
          field.selectionSet value none =
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          fieldType [field] value := by
  intro fieldType
  induction fieldType with
  | named typeName =>
      intro depth value hchildren
      cases depth with
      | zero =>
          cases value <;>
            simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
              GraphQL.Execution.completeValue, outOfFuel]
      | succ childDepth =>
          cases value with
          | null =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | scalar value =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | object runtimeType identity =>
              simpa [GraphQL.Execution.mergedFieldSelectionSet] using
                completeValue_object_group_eq_spec_of_guarded_merged_child_state
                  schema
                  resolvers variableValues childDepth typeName runtimeType
                  identity [field]
                  (by
                    intro hincludes
                    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
                      hchildren childDepth runtimeType identity
                        (Nat.lt_succ_self childDepth) hincludes)
          | list values =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
  | list inner ih =>
      intro depth value hchildren
      cases depth with
      | zero =>
          cases value <;>
            simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
              GraphQL.Execution.completeValue, outOfFuel]
      | succ childDepth =>
          cases value with
          | null =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | scalar value =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | object runtimeType identity =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | list values =>
              have hlist :
                  completeValueList schema resolvers variableValues childDepth
                    inner field.selectionSet values [] =
                  GraphQL.Execution.completeValueList schema resolvers
                    variableValues childDepth inner [field] values := by
                induction values with
                | nil =>
                    simp [completeValueList, GraphQL.Execution.completeValueList]
                | cons value rest ihValues =>
                    have hhead :
                        completeValue schema resolvers variableValues
                          childDepth inner field.selectionSet value
                          none =
                        GraphQL.Execution.completeValue schema resolvers
                          variableValues childDepth inner [field] value :=
                      ih childDepth value (by
                        intro grandChildDepth runtimeType identity hlt
                          hincludes
                        exact hchildren grandChildDepth runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          hincludes)
                    have htail :
                        completeValueList schema resolvers variableValues
                          childDepth inner field.selectionSet rest [] =
                        GraphQL.Execution.completeValueList schema resolvers
                          variableValues childDepth inner [field] rest :=
                      ihValues
                    simp [completeValueList, GraphQL.Execution.completeValueList, hhead, htail, GraphQL.Execution.Result.combine]
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue, reuseOrCreateList?, hlist,
                catchBubbleAsNull, GraphQL.Execution.catchBubbleAsNull]
  | nonNull inner ih =>
      intro depth value hchildren
      cases depth with
      | zero =>
          cases value <;>
            simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
              GraphQL.Execution.completeValue, outOfFuel]
      | succ childDepth =>
          have hinner :
              completeValue schema resolvers variableValues (childDepth + 1)
                inner field.selectionSet value none =
              GraphQL.Execution.completeValue schema resolvers variableValues
                (childDepth + 1) inner [field] value :=
            ih (childDepth + 1) value (by
              intro grandChildDepth runtimeType identity hlt hincludes
              exact hchildren grandChildDepth runtimeType identity hlt
                hincludes)
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue, hinner]

theorem completeValue_single_field_eq_spec_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (field : ExecutableField) :
    ∀ (fieldType : TypeRef) (depth : Nat)
      (value : ResolverValue ObjectIdentity),
      (∀ childDepth runtimeType (identity : ObjectIdentity),
        childDepth < depth ->
        ValueContainsObject value runtimeType identity ->
        schema.typeIncludesObjectBool fieldType.namedType runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] }) ->
        completeValue schema resolvers variableValues depth fieldType
          field.selectionSet value none =
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          fieldType [field] value := by
  intro fieldType
  induction fieldType with
  | named typeName =>
      intro depth value hchildren
      cases depth with
      | zero =>
          cases value <;>
            simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
              GraphQL.Execution.completeValue, outOfFuel]
      | succ childDepth =>
          cases value with
          | null =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | scalar value =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | object runtimeType identity =>
              simpa [GraphQL.Execution.mergedFieldSelectionSet] using
                completeValue_object_group_eq_spec_of_guarded_merged_child_state
                  schema
                  resolvers variableValues childDepth typeName runtimeType
                  identity [field]
                  (by
                    intro hincludes
                    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
                      hchildren childDepth runtimeType identity
                        (Nat.lt_succ_self childDepth)
                        ValueContainsObject.here hincludes)
          | list values =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
  | list inner ih =>
      intro depth value hchildren
      cases depth with
      | zero =>
          cases value <;>
            simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
              GraphQL.Execution.completeValue, outOfFuel]
      | succ childDepth =>
          cases value with
          | null =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | scalar value =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | object runtimeType identity =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | list values =>
              have hlist :
                  completeValueList schema resolvers variableValues childDepth
                    inner field.selectionSet values [] =
                  GraphQL.Execution.completeValueList schema resolvers
                    variableValues childDepth inner [field] values := by
                induction values with
                | nil =>
                    simp [completeValueList, GraphQL.Execution.completeValueList]
                | cons value rest ihValues =>
                    have hhead :
                        completeValue schema resolvers variableValues
                          childDepth inner field.selectionSet value
                          none =
                        GraphQL.Execution.completeValue schema resolvers
                          variableValues childDepth inner [field] value :=
                      ih childDepth value (by
                        intro grandChildDepth runtimeType identity hlt
                          hcontains hincludes
                        exact hchildren grandChildDepth runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          (ValueContainsObject.list (by simp) hcontains)
                          hincludes)
                    have htail :
                        completeValueList schema resolvers variableValues
                          childDepth inner field.selectionSet rest [] =
                        GraphQL.Execution.completeValueList schema resolvers
                          variableValues childDepth inner [field] rest := by
                      apply ihValues
                      intro grandChildDepth runtimeType identity hlt hcontains
                        hincludes
                      have hcontainsCons :
                          ValueContainsObject (.list (value :: rest))
                            runtimeType identity := by
                        cases hcontains with
                        | list hmem hvalue =>
                            exact ValueContainsObject.list (by simp [hmem])
                              hvalue
                      exact hchildren grandChildDepth runtimeType identity hlt
                        hcontainsCons hincludes
                    simp [completeValueList, GraphQL.Execution.completeValueList, hhead, htail, GraphQL.Execution.Result.combine]
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue, reuseOrCreateList?, hlist,
                catchBubbleAsNull, GraphQL.Execution.catchBubbleAsNull]
  | nonNull inner ih =>
      intro depth value hchildren
      cases depth with
      | zero =>
          cases value <;>
            simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
              GraphQL.Execution.completeValue, outOfFuel]
      | succ childDepth =>
          have hinner :
              completeValue schema resolvers variableValues (childDepth + 1)
                inner field.selectionSet value none =
              GraphQL.Execution.completeValue schema resolvers variableValues
                (childDepth + 1) inner [field] value :=
            ih (childDepth + 1) value (by
              intro grandChildDepth runtimeType identity hlt hcontains
                hincludes
              exact hchildren grandChildDepth runtimeType identity hlt
                hcontains hincludes)
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue, hinner]

theorem executeRootSelectionSet_single_field_succ_eq_spec_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
              initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      [.field responseName fieldName arguments directives selectionSet] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet] := by
  apply executeRootSelectionSet_single_field_succ_eq_spec_of_completeValue
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments directives selectionSet hallowed
  cases hlookup : schema.lookupField parentType fieldName with
  | none =>
      simp [executeField, GraphQL.Execution.executeField, executableField,
        hlookup, GraphQL.Execution.singleFieldResult]
  | some fieldDefinition =>
      cases resolved with
      | none =>
          simp [executeField, GraphQL.Execution.executeField, executableField,
            reusablePreviousValue?_none, hlookup, hresolve,
            GraphQL.Execution.singleFieldResult]
      | some resolvedValue =>
          have hcomplete :
              completeValue schema resolvers variableValues depth
                fieldDefinition.outputType selectionSet resolvedValue
                none =
              GraphQL.Execution.completeValue schema resolvers variableValues
                depth fieldDefinition.outputType
                [executableField parentType responseName fieldName arguments
                  selectionSet]
                resolvedValue :=
            completeValue_single_field_eq_spec_of_guarded_child_states schema
              resolvers variableValues
              (executableField parentType responseName fieldName arguments
                selectionSet)
              fieldDefinition.outputType depth resolvedValue
              (by
                intro childDepth runtimeType identity hlt _hincludes
                exact hchildren childDepth runtimeType identity hlt)
          simpa [executeField, GraphQL.Execution.executeField, executableField,
            reusablePreviousValue?_none, hlookup, hresolve,
            GraphQL.Execution.singleFieldResult] using
            congrArg (GraphQL.Execution.singleFieldResult responseName)
              hcomplete

theorem executeRootSelectionSet_single_field_succ_eq_spec_of_guarded_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := selectionSet }
              initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      [.field responseName fieldName arguments directives selectionSet] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet] := by
  apply executeRootSelectionSet_single_field_succ_eq_spec_of_completeValue
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments directives selectionSet hallowed
  cases hlookup : schema.lookupField parentType fieldName with
  | none =>
      simp [executeField, GraphQL.Execution.executeField, executableField,
        hlookup, GraphQL.Execution.singleFieldResult]
  | some fieldDefinition =>
      cases resolved with
      | none =>
          simp [executeField, GraphQL.Execution.executeField, executableField,
            reusablePreviousValue?_none, hlookup, hresolve,
            GraphQL.Execution.singleFieldResult]
      | some resolvedValue =>
          have hcomplete :
              completeValue schema resolvers variableValues depth
                fieldDefinition.outputType selectionSet resolvedValue
                none =
              GraphQL.Execution.completeValue schema resolvers variableValues
                depth fieldDefinition.outputType
                [executableField parentType responseName fieldName arguments
                  selectionSet]
                resolvedValue :=
            completeValue_single_field_eq_spec_of_guarded_child_states schema
              resolvers variableValues
              (executableField parentType responseName fieldName arguments
                selectionSet)
              fieldDefinition.outputType depth resolvedValue
              (by
                intro childDepth runtimeType identity hlt hincludes
                exact hchildren childDepth runtimeType identity hlt
                  (by simpa [Schema.fieldReturnType?, hlookup] using hincludes))
          simpa [executeField, GraphQL.Execution.executeField, executableField,
            reusablePreviousValue?_none, hlookup, hresolve,
            GraphQL.Execution.singleFieldResult] using
            congrArg (GraphQL.Execution.singleFieldResult responseName)
              hcomplete

theorem executeRootSelectionSet_single_field_succ_eq_spec_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := selectionSet }
              initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      [.field responseName fieldName arguments directives selectionSet] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet] := by
  apply executeRootSelectionSet_single_field_succ_eq_spec_of_completeValue
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments directives selectionSet hallowed
  cases hlookup : schema.lookupField parentType fieldName with
  | none =>
      simp [executeField, GraphQL.Execution.executeField, executableField,
        hlookup, GraphQL.Execution.singleFieldResult]
  | some fieldDefinition =>
      cases resolved with
      | none =>
          simp [executeField, GraphQL.Execution.executeField, executableField,
            reusablePreviousValue?_none, hlookup, hresolve,
            GraphQL.Execution.singleFieldResult]
      | some resolvedValue =>
          have hcomplete :
              completeValue schema resolvers variableValues depth
                fieldDefinition.outputType selectionSet resolvedValue
                none =
              GraphQL.Execution.completeValue schema resolvers variableValues
                depth fieldDefinition.outputType
                [executableField parentType responseName fieldName arguments
                  selectionSet]
                resolvedValue :=
            completeValue_single_field_eq_spec_of_contained_child_states schema
              resolvers variableValues
              (executableField parentType responseName fieldName arguments
                selectionSet)
              fieldDefinition.outputType depth resolvedValue
              (by
                intro childDepth runtimeType identity hlt hcontains hincludes
                exact hchildren childDepth runtimeType identity hlt hcontains
                  (by simpa [Schema.fieldReturnType?, hlookup] using hincludes))
          simpa [executeField, GraphQL.Execution.executeField, executableField,
            reusablePreviousValue?_none, hlookup, hresolve,
            GraphQL.Execution.singleFieldResult] using
            congrArg (GraphQL.Execution.singleFieldResult responseName)
              hcomplete

theorem AppendAllowedFieldState.of_child_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendAllowedFieldState schema resolvers variableValues (depth + 1)
      parentType source left responseName fieldName arguments directives
      selectionSet depth := by
  refine
    { depth_eq := rfl
      allowed := hallowed
      rightEquivalent := ?_
      namesDisjoint := hdisjoint }
  exact
    stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
      variableValues (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet]
      (executeRootSelectionSet_single_field_succ_eq_spec_of_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments directives selectionSet resolved hallowed hresolve
        hchildren)

theorem AppendAllowedFieldState.of_guarded_child_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          runtimeType = true ->
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
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendAllowedFieldState schema resolvers variableValues (depth + 1)
      parentType source left responseName fieldName arguments directives
      selectionSet depth := by
  refine
    { depth_eq := rfl
      allowed := hallowed
      rightEquivalent := ?_
      namesDisjoint := hdisjoint }
  exact
    stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
      variableValues (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet]
      (executeRootSelectionSet_single_field_succ_eq_spec_of_guarded_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments directives selectionSet resolved hallowed hresolve
        hchildren)

theorem AppendAllowedFieldState.of_contained_child_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          runtimeType = true ->
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
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendAllowedFieldState schema resolvers variableValues (depth + 1)
      parentType source left responseName fieldName arguments directives
      selectionSet depth := by
  refine
    { depth_eq := rfl
      allowed := hallowed
      rightEquivalent := ?_
      namesDisjoint := hdisjoint }
  exact
    stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
      variableValues (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet]
      (executeRootSelectionSet_single_field_succ_eq_spec_of_contained_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments directives selectionSet resolved hallowed hresolve
        hchildren)

theorem AppendSelectionState.field_allowed_of_child_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendSelectionState schema resolvers variableValues (depth + 1)
      parentType source left
      (.field responseName fieldName arguments directives selectionSet) :=
  AppendSelectionState.field_allowed
    (AppendAllowedFieldState.of_child_states hallowed hresolve hchildren
      hdisjoint)

theorem AppendSelectionState.field_allowed_of_guarded_child_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          runtimeType = true ->
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
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendSelectionState schema resolvers variableValues (depth + 1)
      parentType source left
      (.field responseName fieldName arguments directives selectionSet) :=
  AppendSelectionState.field_allowed
    (AppendAllowedFieldState.of_guarded_child_states hallowed hresolve
      hchildren hdisjoint)

theorem AppendSelectionState.field_allowed_of_contained_child_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          runtimeType = true ->
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
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendSelectionState schema resolvers variableValues (depth + 1)
      parentType source left
      (.field responseName fieldName arguments directives selectionSet) :=
  AppendSelectionState.field_allowed
    (AppendAllowedFieldState.of_contained_child_states hallowed hresolve
      hchildren hdisjoint)

theorem AppendAllowedFieldState.of_child_selectionSet_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
        childDepth < depth ->
          AppendSelectionSetState schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) [] selectionSet)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendAllowedFieldState schema resolvers variableValues (depth + 1)
      parentType source left responseName fieldName arguments directives
      selectionSet depth :=
  AppendAllowedFieldState.of_child_states hallowed hresolve
    (by
      intro childDepth runtimeType identity hlt
      exact stateEquivalent_of_selectionSet_state
        (hchildren childDepth runtimeType identity hlt))
    hdisjoint

theorem AppendSelectionState.field_allowed_of_child_selectionSet_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
        childDepth < depth ->
          AppendSelectionSetState schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) [] selectionSet)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendSelectionState schema resolvers variableValues (depth + 1)
      parentType source left
      (.field responseName fieldName arguments directives selectionSet) :=
  AppendSelectionState.field_allowed
    (AppendAllowedFieldState.of_child_selectionSet_states hallowed hresolve
      hchildren hdisjoint)

theorem AppendAllowedFieldState.of_child_prefix_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
        childDepth < depth ->
          AppendSelectionSetPrefixState schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity) []
            selectionSet)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendAllowedFieldState schema resolvers variableValues (depth + 1)
      parentType source left responseName fieldName arguments directives
      selectionSet depth :=
  AppendAllowedFieldState.of_child_states hallowed hresolve
    (by
      intro childDepth runtimeType identity hlt
      exact stateEquivalent_of_selectionSet_prefix_state
        (hchildren childDepth runtimeType identity hlt))
    hdisjoint

theorem AppendSelectionState.field_allowed_of_child_prefix_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
        childDepth < depth ->
          AppendSelectionSetPrefixState schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity) []
            selectionSet)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendSelectionState schema resolvers variableValues (depth + 1)
      parentType source left
      (.field responseName fieldName arguments directives selectionSet) :=
  AppendSelectionState.field_allowed
    (AppendAllowedFieldState.of_child_prefix_states hallowed hresolve
      hchildren hdisjoint)

theorem AppendSelectionState.field_allowed_of_child_prefix_states_fresh
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
        childDepth < depth ->
          AppendSelectionSetPrefixState schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity) []
            selectionSet)
    (hfresh :
      responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left).map Prod.fst) :
    AppendSelectionState schema resolvers variableValues (depth + 1)
      parentType source left
      (.field responseName fieldName arguments directives selectionSet) :=
  AppendSelectionState.field_allowed_of_child_prefix_states hallowed hresolve
    hchildren
    (executableGroupNamesDisjoint_single_field_of_responseName_fresh schema
      variableValues parentType source left responseName fieldName arguments
      directives selectionSet hallowed hfresh)

theorem executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
              initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source (executableFieldSelections [field]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source (executableFieldSelections [field]) := by
  cases field with
  | mk fieldParent responseName fieldName arguments selectionSet =>
      dsimp [executableFieldSelections, executableFieldSelection] at hparent hresolve hchildren ⊢
      subst fieldParent
      exact executeRootSelectionSet_single_field_succ_eq_spec_of_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments [] selectionSet resolved rfl hresolve hchildren

theorem executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_guarded_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source (executableFieldSelections [field]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source (executableFieldSelections [field]) := by
  cases field with
  | mk fieldParent responseName fieldName arguments selectionSet =>
      dsimp [executableFieldSelections, executableFieldSelection] at hparent hresolve hchildren ⊢
      subst fieldParent
      exact executeRootSelectionSet_single_field_succ_eq_spec_of_guarded_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments [] selectionSet resolved rfl hresolve hchildren

theorem executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source (executableFieldSelections [field]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source (executableFieldSelections [field]) := by
  cases field with
  | mk fieldParent responseName fieldName arguments selectionSet =>
      dsimp [executableFieldSelections, executableFieldSelection] at hparent hresolve hchildren ⊢
      subst fieldParent
      exact executeRootSelectionSet_single_field_succ_eq_spec_of_contained_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments [] selectionSet resolved rfl hresolve hchildren

theorem ExecutableFieldsFlatSpecEquivalent_single_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
              initial := .object [] }) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [field] := by
  unfold ExecutableFieldsFlatSpecEquivalent
  exact executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_child_states
    schema resolvers variableValues depth parentType source field resolved
    hparent hresolve hchildren

theorem ExecutableFieldsFlatSpecEquivalent_single_of_guarded_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [field] := by
  unfold ExecutableFieldsFlatSpecEquivalent
  exact executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_guarded_child_states
    schema resolvers variableValues depth parentType source field resolved
    hparent hresolve hchildren

theorem ExecutableFieldsFlatSpecEquivalent_single_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [field] := by
  unfold ExecutableFieldsFlatSpecEquivalent
  exact executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_contained_child_states
    schema resolvers variableValues depth parentType source field resolved
    hparent hresolve hchildren

theorem ExecutableFieldsFlatSpecEquivalent_collected_single_field_group_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (hgroup : (responseName, [field]) ∈ groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
              initial := .object [] }) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [field] := by
  have hgroupParents : ExecutableFieldsParent parentType [field] :=
    hparents responseName [field] hgroup
  have hparent : field.parentType = parentType :=
    hgroupParents field (by simp)
  exact ExecutableFieldsFlatSpecEquivalent_single_of_child_states
    schema resolvers variableValues depth parentType source field
    (resolvers.resolve field.parentType field.fieldName field.arguments source)
    hparent rfl hchildren

theorem ExecutableGroupsFlatSpecEquivalent_single_field_group_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType responseName : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField)
    (hparent : field.parentType = parentType)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
              initial := .object [] }) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, [field])] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableFields]
  exact ExecutableFieldsFlatSpecEquivalent_single_of_child_states
    schema resolvers variableValues depth parentType source field
    (resolvers.resolve field.parentType field.fieldName field.arguments source)
    hparent rfl hchildren

theorem executeRootSelectionSet_executableFieldSelections_group_eq_spec_of_merged_complete
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
    (_hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hungrouped :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections (field :: fields)) =
      GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName (field :: fields)) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source (executableFieldSelections (field :: fields)) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      (executableFieldSelections (field :: fields)) := by
  have hspecRoot :
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source
          (executableFieldSelections (field :: fields)) =
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        (depth + 1) source [(responseName, field :: fields)] :=
    specExecuteRootSelectionSet_executableFieldSelections_same_group schema
      resolvers variableValues (depth + 1) parentType source responseName
      field fields hresponse hparent
  have hspecField :
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
          (depth + 1) source [(responseName, field :: fields)] =
      GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName (field :: fields) := by
    cases hfield :
        GraphQL.Execution.executeField schema resolvers variableValues
          (depth + 1) source responseName (field :: fields) <;>
      simp [GraphQL.Execution.executeCollectedFields, Result.combine,
        GraphQL.Execution.Result.combine, hfield]
  exact hungrouped.trans (hspecRoot.trans hspecField).symm

theorem executeRootSelectionSet_executableFieldSelections_single_eq_merged_complete_of_child_states
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
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
              initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source (executableFieldSelections [field]) =
    GraphQL.Execution.executeField schema resolvers variableValues
      (depth + 1) source responseName [field] := by
  have hroot :=
    executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_child_states
      schema resolvers variableValues depth parentType source field resolved
      hparent hresolve hchildren
  have hresponseGroup :
      ∀ candidate, candidate ∈ [field] ->
        candidate.responseName = responseName := by
    intro candidate hmem
    have hcandidate : candidate = field := by
      simpa using hmem
    rw [hcandidate]
    exact hresponse
  have hparentGroup :
      ∀ candidate, candidate ∈ [field] ->
        candidate.parentType = parentType := by
    intro candidate hmem
    have hcandidate : candidate = field := by
      simpa using hmem
    rw [hcandidate]
    exact hparent
  have hspecRoot :
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source (executableFieldSelections [field]) =
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        (depth + 1) source [(responseName, [field])] :=
    specExecuteRootSelectionSet_executableFieldSelections_same_group schema
      resolvers variableValues (depth + 1) parentType source responseName
      field [] hresponseGroup hparentGroup
  have hspecField :
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
          (depth + 1) source [(responseName, [field])] =
      GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName [field] := by
    cases hfield :
        GraphQL.Execution.executeField schema resolvers variableValues
          (depth + 1) source responseName [field] <;>
      simp [GraphQL.Execution.executeCollectedFields, Result.combine,
        GraphQL.Execution.Result.combine, hfield]
  exact hroot.trans (hspecRoot.trans hspecField)

theorem executeRootSelectionSet_executableFieldSelections_single_eq_merged_complete_of_contained_child_states
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
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source (executableFieldSelections [field]) =
    GraphQL.Execution.executeField schema resolvers variableValues
      (depth + 1) source responseName [field] := by
  have hroot :=
    executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_contained_child_states
      schema resolvers variableValues depth parentType source field resolved
      hparent hresolve hchildren
  have hresponseGroup :
      ∀ candidate, candidate ∈ [field] ->
        candidate.responseName = responseName := by
    intro candidate hmem
    have hcandidate : candidate = field := by
      simpa using hmem
    rw [hcandidate]
    exact hresponse
  have hparentGroup :
      ∀ candidate, candidate ∈ [field] ->
        candidate.parentType = parentType := by
    intro candidate hmem
    have hcandidate : candidate = field := by
      simpa using hmem
    rw [hcandidate]
    exact hparent
  have hspecRoot :
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source (executableFieldSelections [field]) =
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        (depth + 1) source [(responseName, [field])] :=
    specExecuteRootSelectionSet_executableFieldSelections_same_group schema
      resolvers variableValues (depth + 1) parentType source responseName
      field [] hresponseGroup hparentGroup
  have hspecField :
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
          (depth + 1) source [(responseName, [field])] =
      GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName [field] := by
    cases hfield :
        GraphQL.Execution.executeField schema resolvers variableValues
          (depth + 1) source responseName [field] <;>
      simp [GraphQL.Execution.executeCollectedFields, Result.combine,
        GraphQL.Execution.Result.combine, hfield]
  exact hroot.trans (hspecRoot.trans hspecField)

theorem executeRootSelectionSet_executableFieldSelections_single_eq_merged_complete_of_guarded_child_states
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
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source (executableFieldSelections [field]) =
    GraphQL.Execution.executeField schema resolvers variableValues
      (depth + 1) source responseName [field] := by
  have hroot :=
    executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_guarded_child_states
      schema resolvers variableValues depth parentType source field resolved
      hparent hresolve hchildren
  have hresponseGroup :
      ∀ candidate, candidate ∈ [field] ->
        candidate.responseName = responseName := by
    intro candidate hmem
    have hcandidate : candidate = field := by
      simpa using hmem
    rw [hcandidate]
    exact hresponse
  have hparentGroup :
      ∀ candidate, candidate ∈ [field] ->
        candidate.parentType = parentType := by
    intro candidate hmem
    have hcandidate : candidate = field := by
      simpa using hmem
    rw [hcandidate]
    exact hparent
  have hspecRoot :
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source (executableFieldSelections [field]) =
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        (depth + 1) source [(responseName, [field])] :=
    specExecuteRootSelectionSet_executableFieldSelections_same_group schema
      resolvers variableValues (depth + 1) parentType source responseName
      field [] hresponseGroup hparentGroup
  have hspecField :
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
          (depth + 1) source [(responseName, [field])] =
      GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName [field] := by
    cases hfield :
        GraphQL.Execution.executeField schema resolvers variableValues
          (depth + 1) source responseName [field] <;>
      simp [GraphQL.Execution.executeCollectedFields, Result.combine,
        GraphQL.Execution.Result.combine, hfield]
  exact hroot.trans (hspecRoot.trans hspecField)

theorem ExecutableFieldsMergedComplete_single_of_child_states
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
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
              initial := .object [] }) :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field [] resolved := by
  unfold ExecutableFieldsMergedComplete
  exact
    executeRootSelectionSet_executableFieldSelections_single_eq_merged_complete_of_child_states
      schema resolvers variableValues depth parentType source responseName
      field resolved hresponse hparent hresolve hchildren

theorem ExecutableFieldsMergedComplete_single_of_guarded_child_states
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
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field [] resolved := by
  unfold ExecutableFieldsMergedComplete
  exact
    executeRootSelectionSet_executableFieldSelections_single_eq_merged_complete_of_guarded_child_states
      schema resolvers variableValues depth parentType source responseName
      field resolved hresponse hparent hresolve hchildren

theorem ExecutableFieldsMergedComplete_single_of_contained_child_states
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
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field [] resolved := by
  unfold ExecutableFieldsMergedComplete
  exact
    executeRootSelectionSet_executableFieldSelections_single_eq_merged_complete_of_contained_child_states
      schema resolvers variableValues depth parentType source responseName
      field resolved hresponse hparent hresolve hchildren

theorem ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_merged_complete
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
    (hungrouped :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections (field :: fields)) =
      GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName (field :: fields)) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source (field :: fields) := by
  unfold ExecutableFieldsFlatSpecEquivalent
  exact executeRootSelectionSet_executableFieldSelections_group_eq_spec_of_merged_complete
    schema resolvers variableValues depth parentType source responseName field
    fields resolved hresponse hparent hresolve hungrouped

theorem ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_mergedComplete
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
    (hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields resolved) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source (field :: fields) := by
  unfold ExecutableFieldsMergedComplete at hmerged
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_merged_complete
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresponse hparent hresolve hmerged

theorem ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_merged_complete
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
    (hungrouped :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections (field :: fields)) =
      GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName (field :: fields)) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, field :: fields)] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableFields]
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_merged_complete
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresponse hparent hresolve hungrouped

theorem ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_mergedComplete
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
    (hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields resolved) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, field :: fields)] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableFields]
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_mergedComplete
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresponse hparent hresolve hmerged

theorem ExecutableGroupsFlatSpecEquivalent_collected_nonempty_group_of_merged_complete
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
    (hungrouped :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections (field :: fields)) =
      GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName (field :: fields)) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, field :: fields)] := by
  have hgroupResponses :
      ExecutableFieldsResponseName responseName (field :: fields) :=
    hresponses responseName (field :: fields) hgroup
  have hgroupParents :
      ExecutableFieldsParent parentType (field :: fields) :=
    hparents responseName (field :: fields) hgroup
  exact
    ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_merged_complete
      schema resolvers variableValues depth parentType source responseName
      field fields
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      hgroupResponses hgroupParents rfl hungrouped

theorem executeRootSelectionSet_eq_spec_of_exact_nonempty_group_merged_complete
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
    (hungrouped :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections (field :: fields)) =
      GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName (field :: fields)) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  have hgroups :
      ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet) := by
    rw [hcollect]
    exact
      ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_merged_complete
        schema resolvers variableValues depth parentType source responseName
        field fields
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        hresponse hparent rfl hungrouped
  exact
    executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
      schema resolvers variableValues (depth + 1) parentType source
      selectionSet hdirect hgroups

theorem executeRootSelectionSet_eq_spec_of_exact_nonempty_group_mergedComplete
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
    (hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  unfold ExecutableFieldsMergedComplete at hmerged
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_merged_complete
      schema resolvers variableValues depth parentType source selectionSet
      responseName field fields hcollect hdirect hresponse hparent hmerged

theorem executeQueryAtDepth_eq_spec_of_exact_nonempty_group_merged_complete
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
    (hungrouped :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        operation.rootType source
        (executableFieldSelections (field :: fields)) =
      GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName (field :: fields)) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_merged_complete
      schema resolvers variableValues depth operation.rootType source
      operation.selectionSet responseName field fields hcollect hdirect
      hresponse hparent hungrouped

theorem executeQueryAtDepth_eq_spec_of_exact_nonempty_group_mergedComplete
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
    (hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        operation.rootType source responseName field fields
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_mergedComplete
      schema resolvers variableValues depth operation.rootType source
      operation.selectionSet responseName field fields hcollect hdirect
      hresponse hparent hmerged

theorem executeQuery_eq_spec_of_exact_nonempty_group_merged_complete
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
    (hungrouped :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        operation.rootType source
        (executableFieldSelections (field :: fields)) =
      GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName (field :: fields)) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_exact_nonempty_group_merged_complete
      schema resolvers variableValues operation depth source responseName field
      fields hroot hcollect hdirect hresponse hparent hungrouped

theorem executeQuery_eq_spec_of_exact_nonempty_group_mergedComplete
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
    (hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        operation.rootType source responseName field fields
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_exact_nonempty_group_mergedComplete
      schema resolvers variableValues operation depth source responseName field
      fields hroot hcollect hdirect hresponse hparent hmerged

theorem executeRootSelectionSet_eq_spec_of_exact_single_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [(responseName, [field])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hparent : field.parentType = parentType)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
              initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  have hgroups :
      ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet) := by
    rw [hcollect]
    exact
      ExecutableGroupsFlatSpecEquivalent_single_field_group_of_child_states
        schema resolvers variableValues depth parentType responseName source
        field hparent hchildren
  exact
    executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
      schema resolvers variableValues (depth + 1) parentType source
      selectionSet hdirect hgroups

theorem stateEquivalent_of_exact_single_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [(responseName, [field])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hparent : field.parentType = parentType)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues (depth + 1) parentType source selectionSet
    (executeRootSelectionSet_eq_spec_of_exact_single_field_group schema
      resolvers variableValues depth parentType source selectionSet
      responseName field hcollect hdirect hparent hchildren)

theorem stateEquivalent_of_collected_single_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, [field]) ∈ groups)
    (hexact : groups = [(responseName, [field])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
  have hparents : CollectedGroupsParent parentType groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.parent_of_collect_eq state groups
        hcollect
  have hparent : field.parentType = parentType :=
    (hparents responseName [field] hgroup) field (by simp)
  exact
    stateEquivalent_of_exact_single_field_group schema resolvers
      variableValues depth parentType source selectionSet responseName field
      (by simpa [hexact] using hcollect) hdirect hparent hchildren

theorem executeQueryAtDepth_eq_spec_of_exact_single_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, [field])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hparent : field.parentType = operation.rootType)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
              initial := .object [] }) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_state_equivalent schema resolvers
    variableValues operation (depth + 1) source hroot
  exact stateEquivalent_of_exact_single_field_group schema resolvers
    variableValues depth operation.rootType source operation.selectionSet
    responseName field hcollect hdirect hparent hchildren

theorem executeQuery_eq_spec_of_exact_single_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, [field])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hparent : field.parentType = operation.rootType)
    (hchildren :
      ∀ childDepth runtimeType (identity : ObjectIdentity),
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
              initial := .object [] }) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact executeQueryAtDepth_eq_spec_of_exact_single_field_group schema
    resolvers variableValues operation depth source responseName field hroot
    hcollect hdirect hparent hchildren

end ExecutionUngrouped
end Algorithms

end GraphQL
