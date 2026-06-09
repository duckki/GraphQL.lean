import GraphQL.DataModel.Store
import GraphQL.SchemaWellFormedness.PossibleObjectImplementation

/-!
Store-backed resolved-value inclusion lemmas.
-/
namespace GraphQL

namespace DataModel

namespace Store

private def storeValueObjectsInclude (schema : Schema) (parentType : Name) :
    Value -> Prop
  | .object runtimeType _identity =>
      schema.typeIncludesObjectBool parentType runtimeType = true
  | .list values =>
      ∀ value, value ∈ values ->
        storeValueObjectsInclude schema parentType value
  | _ => True

def executionValueObjectsInclude {ObjectIdentity : Type}
    (schema : Schema) (parentType : Name) :
    Execution.Value ObjectIdentity -> Prop
  | .object runtimeType _identity =>
      schema.typeIncludesObjectBool parentType runtimeType = true
  | .list values =>
      ∀ value, value ∈ values ->
        executionValueObjectsInclude schema parentType value
  | _ => True

private theorem storeValueObjectsInclude_mono
    (schema : Schema) {left right : Name} :
    (∀ runtimeType,
      schema.typeIncludesObjectBool left runtimeType = true ->
        schema.typeIncludesObjectBool right runtimeType = true) ->
      ∀ value,
        storeValueObjectsInclude schema left value ->
          storeValueObjectsInclude schema right value
  | hsubtype, .null, _hinclude => by
      simp [storeValueObjectsInclude]
  | hsubtype, .scalar _value, _hinclude => by
      simp [storeValueObjectsInclude]
  | hsubtype, .object runtimeType _identity, hinclude => by
      simpa [storeValueObjectsInclude] using
        hsubtype runtimeType
          (by simpa [storeValueObjectsInclude] using hinclude)
  | hsubtype, .list values, hinclude => by
      have hinclude' :
          ∀ value, value ∈ values ->
            storeValueObjectsInclude schema left value := by
        simpa [storeValueObjectsInclude] using hinclude
      simp [storeValueObjectsInclude]
      intro value hvalue
      exact storeValueObjectsInclude_mono schema hsubtype value
        (hinclude' value hvalue)

private theorem executionValueObjectsInclude_mono
    {ObjectIdentity : Type}
    (schema : Schema) {left right : Name} :
    (∀ runtimeType,
      schema.typeIncludesObjectBool left runtimeType = true ->
        schema.typeIncludesObjectBool right runtimeType = true) ->
      ∀ value : Execution.Value ObjectIdentity,
        executionValueObjectsInclude schema left value ->
          executionValueObjectsInclude schema right value
  | hsubtype, .null, _hinclude => by
      simp [executionValueObjectsInclude]
  | hsubtype, .scalar _value, _hinclude => by
      simp [executionValueObjectsInclude]
  | hsubtype, .object runtimeType _identity, hinclude => by
      simpa [executionValueObjectsInclude] using
        hsubtype runtimeType
          (by simpa [executionValueObjectsInclude] using hinclude)
  | hsubtype, .list values, hinclude => by
      have hinclude' :
          ∀ value, value ∈ values ->
            executionValueObjectsInclude schema left value := by
        simpa [executionValueObjectsInclude] using hinclude
      simp [executionValueObjectsInclude]
      intro value hvalue
      exact executionValueObjectsInclude_mono schema hsubtype value
        (hinclude' value hvalue)

private theorem storeValueObjectsInclude_toExecutionValue
    (schema : Schema) (parentType : Name) :
    ∀ value,
      storeValueObjectsInclude schema parentType value ->
        executionValueObjectsInclude schema parentType
          value.toExecutionValue
  | .null, _hinclude => by
      simp [Value.toExecutionValue, executionValueObjectsInclude]
  | .scalar _value, _hinclude => by
      simp [Value.toExecutionValue, executionValueObjectsInclude]
  | .object _runtimeType _identity, hinclude => by
      simpa [Value.toExecutionValue, executionValueObjectsInclude,
        storeValueObjectsInclude] using hinclude
  | .list values, hinclude => by
      have hinclude' :
          ∀ value, value ∈ values ->
            storeValueObjectsInclude schema parentType value := by
        simpa [storeValueObjectsInclude] using hinclude
      simp [Value.toExecutionValue, executionValueObjectsInclude]
      intro value hvalue
      exact storeValueObjectsInclude_toExecutionValue schema parentType value
        (hinclude' value hvalue)

private theorem storeValueObjectsInclude_of_conformsToType
    (schema : Schema) :
    ∀ value typeRef,
      Value.conformsToType schema value typeRef ->
        storeValueObjectsInclude schema typeRef.namedType value
  | .null, .named _typeName, _hconforms => by
      simp [storeValueObjectsInclude]
  | .null, .list _inner, _hconforms => by
      simp [storeValueObjectsInclude]
  | .null, .nonNull _inner, hconforms => by
      cases hconforms
  | .scalar _value, .named _typeName, _hconforms => by
      simp [storeValueObjectsInclude]
  | .scalar value, .nonNull inner, hconforms => by
      exact storeValueObjectsInclude_of_conformsToType schema
        (.scalar value) inner hconforms
  | .scalar _value, .list _inner, hconforms => by
      cases hconforms
  | .object runtimeType identity, .named typeName, hconforms => by
      simpa [storeValueObjectsInclude] using
        (show schema.typeIncludesObjectBool typeName runtimeType = true from
          List.contains_iff_mem.mpr hconforms)
  | .object runtimeType identity, .nonNull inner, hconforms => by
      simpa [TypeRef.namedType, storeValueObjectsInclude] using
        storeValueObjectsInclude_of_conformsToType schema
          (.object runtimeType identity) inner hconforms
  | .object _runtimeType _identity, .list _inner, hconforms => by
      cases hconforms
  | .list values, .list inner, hconforms => by
      simp [TypeRef.namedType, storeValueObjectsInclude]
      intro value hvalue
      exact storeValueObjectsInclude_of_conformsToType schema value inner
        (hconforms value hvalue)
  | .list values, .nonNull inner, hconforms => by
      simpa [TypeRef.namedType, storeValueObjectsInclude] using
        storeValueObjectsInclude_of_conformsToType schema
          (.list values) inner hconforms
  | .list _values, .named _typeName, hconforms => by
      cases hconforms

private theorem storeValueObjectsInclude_list_map_edges
    (schema : Schema) (parentType : Name)
    (edges : List ObjectEdge) :
    (∀ edge, edge ∈ edges ->
      schema.typeIncludesObjectBool parentType edge.targetType = true) ->
      storeValueObjectsInclude schema parentType
        (.list (edges.map
          (fun edge => Value.object edge.targetType edge.targetPath))) := by
  intro hedges
  simp [storeValueObjectsInclude]
  intro edge hedge
  exact hedges edge hedge

private theorem mem_insertEdgeByIndex_self_or_mem
    (edge candidate : ObjectEdge) :
    ∀ edges,
      edge ∈ insertEdgeByIndex candidate edges ->
        edge = candidate ∨ edge ∈ edges
  | [], hmem => by
      simp [insertEdgeByIndex] at hmem
      exact Or.inl hmem
  | head :: rest, hmem => by
      by_cases hle : candidate.index?.getD 0 <= head.index?.getD 0
      · simp [insertEdgeByIndex, hle] at hmem
        exact hmem.elim Or.inl (fun htail => Or.inr (by simpa using htail))
      · have hgt : ¬ candidate.index?.getD 0 <= head.index?.getD 0 :=
          hle
        simp [insertEdgeByIndex, hgt] at hmem
        rcases hmem with hhead | hinserted
        · exact Or.inr (by simp [hhead])
        · rcases mem_insertEdgeByIndex_self_or_mem edge candidate rest
            hinserted with hcandidate | hrest
          · exact Or.inl hcandidate
          · exact Or.inr (by simp [hrest])

private theorem mem_sortEdgesByIndex_mem
    (edge : ObjectEdge) :
    ∀ edges,
      edge ∈ sortEdgesByIndex edges ->
        edge ∈ edges
  | [], hmem => by
      simp [sortEdgesByIndex] at hmem
  | head :: rest, hmem => by
      simp [sortEdgesByIndex] at hmem
      rcases mem_insertEdgeByIndex_self_or_mem edge head
          (sortEdgesByIndex rest) hmem with hhead | hrest
      · simp [hhead]
      · exact List.mem_cons_of_mem head
          (mem_sortEdgesByIndex_mem edge rest hrest)

private theorem mem_indexedMatchingEdges_mem_edges
    (store : DataModel.Store) (sourcePath : ObjectPath)
    (field : FieldAccess) (edge : ObjectEdge) :
    edge ∈ store.indexedMatchingEdges sourcePath field ->
      edge ∈ store.edges := by
  intro hmem
  have hunordered :
      edge ∈ store.indexedMatchingEdgesUnsorted sourcePath field :=
    mem_sortEdgesByIndex_mem edge
      (store.indexedMatchingEdgesUnsorted sourcePath field) hmem
  simp [indexedMatchingEdgesUnsorted,
    matchingEdges] at hunordered
  exact hunordered.1

private theorem mem_indexedMatchingEdges_matches
    (store : DataModel.Store) (sourcePath : ObjectPath)
    (field : FieldAccess) (edge : ObjectEdge) :
    edge ∈ store.indexedMatchingEdges sourcePath field ->
      edge.matchesField sourcePath field = true := by
  intro hmem
  have hunordered :
      edge ∈ store.indexedMatchingEdgesUnsorted sourcePath field :=
    mem_sortEdgesByIndex_mem edge
      (store.indexedMatchingEdgesUnsorted sourcePath field) hmem
  simp [indexedMatchingEdgesUnsorted,
    matchingEdges] at hunordered
  exact hunordered.2.2

private theorem firstMatchingEdge?_some_mem
    (store : DataModel.Store) (sourcePath : ObjectPath)
    (field : FieldAccess) (index? : Option Nat)
    (edge : ObjectEdge) :
    store.firstMatchingEdge? sourcePath field index? = some edge ->
      edge ∈ store.edges := by
  intro hlookup
  exact List.mem_of_find?_eq_some hlookup

private theorem firstMatchingEdge?_some_matches
    (store : DataModel.Store) (sourcePath : ObjectPath)
    (field : FieldAccess) (index? : Option Nat)
    (edge : ObjectEdge) :
    store.firstMatchingEdge? sourcePath field index? = some edge ->
      edge.matchesField sourcePath field = true
        ∧ (edge.index? == index?) = true := by
  intro hlookup
  have hpredicate := List.find?_some hlookup
  simpa [firstMatchingEdge?] using hpredicate

private theorem objectEdge_matchesField_sourcePath
    (edge : ObjectEdge) (sourcePath : ObjectPath)
    (field : FieldAccess) :
    edge.matchesField sourcePath field = true ->
      ObjectPath.eqBool edge.sourcePath sourcePath = true := by
  intro hmatch
  simp [ObjectEdge.matchesField] at hmatch
  exact hmatch.1

private theorem objectEdge_matchesField_fieldName
    (edge : ObjectEdge) (sourcePath : ObjectPath)
    (field : FieldAccess) :
    edge.matchesField sourcePath field = true ->
      edge.field.name = field.name := by
  intro hmatch
  simp [ObjectEdge.matchesField, FieldAccess.eqBool] at hmatch
  exact hmatch.2.1

private theorem resolveValue_objectsInclude_of_lookupField_and_edges
    (schema : Schema) (store : DataModel.Store)
    (runtimeType : Name) (identity : ObjectPath)
    (fieldName : Name) (arguments : List Argument)
    (fieldDefinition : FieldDefinition) :
    store.wellTyped schema ->
    schema.lookupField runtimeType fieldName = some fieldDefinition ->
    (let field := fieldAccess fieldName arguments
     ∀ edge, edge ∈ store.edges ->
      edge.matchesField identity field = true ->
        schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
          edge.targetType = true) ->
      storeValueObjectsInclude schema fieldDefinition.outputType.namedType
        (store.resolveValue schema fieldName arguments
          (.object runtimeType identity)) := by
  intro hstore hlookup hedges
  cases hnode : store.lookupNode? identity with
  | none =>
      simp [resolveValue, hnode, storeValueObjectsInclude]
  | some node =>
      by_cases htype : (node.typeName == runtimeType) = true
      · have hnodeType : node.typeName = runtimeType :=
          beq_iff_eq.mp htype
        have hlookupNode :
            schema.lookupField node.typeName fieldName = some fieldDefinition := by
          simpa [hnodeType] using hlookup
        have hnodeWell : node.wellTyped schema :=
          hstore.2.2.2.1 node
            (lookupNode?_some_mem store hnode)
        let field := fieldAccess fieldName arguments
        by_cases hleaf :
            schema.getPossibleTypes
              fieldDefinition.outputType.namedType = []
        · cases hproperty : node.lookupProperty? field with
          | none =>
              simp [resolveValue, hnode, htype, hlookup,
                hleaf, field, hproperty, storeValueObjectsInclude]
          | some property =>
              rcases
                ObjectNode.lookupProperty?_some_conformsToLookupField
                  schema node field property hnodeWell hproperty with
                ⟨storedFieldDefinition, hstoredLookup, _hstoredLeaf,
                  hconforms⟩
              have hdefinitionEq :
                  storedFieldDefinition = fieldDefinition := by
                have hstoredLookup' :
                    schema.lookupField node.typeName fieldName =
                      some storedFieldDefinition := by
                  simpa [field, fieldAccess] using
                    hstoredLookup
                rw [hlookupNode] at hstoredLookup'
                cases hstoredLookup'
                rfl
              subst storedFieldDefinition
              simp [resolveValue, hnode, htype, hlookup,
                hleaf, field, hproperty]
              exact storeValueObjectsInclude_of_conformsToType schema
                property.toValue fieldDefinition.outputType hconforms
        · have hnonempty :
              ¬ schema.getPossibleTypes
                fieldDefinition.outputType.namedType = [] := hleaf
          by_cases hlist :
              typeRefIsListLike fieldDefinition.outputType = true
          · simp [resolveValue, hnode, htype, hlookup,
              hnonempty, hlist]
            apply storeValueObjectsInclude_list_map_edges
            intro edge hedge
            exact hedges edge
              (mem_indexedMatchingEdges_mem_edges store identity field edge hedge)
              (mem_indexedMatchingEdges_matches store identity field edge hedge)
          · cases hedge :
              store.firstMatchingEdge? identity field none with
            | none =>
                simp [resolveValue, hnode, htype, hlookup,
                  hnonempty, hlist, field, hedge, storeValueObjectsInclude]
            | some edge =>
                have hmatches :=
                  (firstMatchingEdge?_some_matches store identity field none
                    edge hedge).1
                have htarget := hedges edge
                  (firstMatchingEdge?_some_mem store identity field none edge
                    hedge)
                  hmatches
                simp [resolveValue, hnode, htype, hlookup,
                  hnonempty, hlist, field, hedge, storeValueObjectsInclude]
                exact htarget
      · have htypeFalse : (node.typeName == runtimeType) = false := by
          cases hmatch : node.typeName == runtimeType
          · rfl
          · exact False.elim (htype hmatch)
        simp [resolveValue, hnode, htypeFalse,
          storeValueObjectsInclude]

mutual
  private theorem structuralInputValueEqBool_symm :
      ∀ left right,
        FieldAccess.structuralInputValueEqBool left right = true ->
          FieldAccess.structuralInputValueEqBool right left = true
    | left, right, h => by
        cases left <;> cases right <;>
          simp [FieldAccess.structuralInputValueEqBool] at h ⊢
        all_goals
          first
          | exact h.symm
          | exact structuralInputValuesEqBool_symm _ _ h
          | exact structuralInputFieldsEqBool_symm _ _ h

  private theorem structuralInputValuesEqBool_symm :
      ∀ left right,
        FieldAccess.structuralInputValuesEqBool left right = true ->
          FieldAccess.structuralInputValuesEqBool right left = true
    | [], [], _h => by
        simp [FieldAccess.structuralInputValuesEqBool]
    | left :: leftRest, right :: rightRest, h => by
        simp [FieldAccess.structuralInputValuesEqBool] at h ⊢
        exact ⟨structuralInputValueEqBool_symm left right h.1,
          structuralInputValuesEqBool_symm leftRest rightRest h.2⟩
    | [], _ :: _, h
    | _ :: _, [], h => by
        simp [FieldAccess.structuralInputValuesEqBool] at h

  private theorem structuralInputFieldsEqBool_symm :
      ∀ left right,
        FieldAccess.structuralInputFieldsEqBool left right = true ->
          FieldAccess.structuralInputFieldsEqBool right left = true
    | [], [], _h => by
        simp [FieldAccess.structuralInputFieldsEqBool]
    | (leftName, leftValue) :: leftRest,
      (rightName, rightValue) :: rightRest, h => by
        simp [FieldAccess.structuralInputFieldsEqBool] at h ⊢
        exact ⟨⟨h.1.1.symm,
          structuralInputValueEqBool_symm leftValue rightValue h.1.2⟩,
          structuralInputFieldsEqBool_symm leftRest rightRest h.2⟩
    | [], _ :: _, h
    | _ :: _, [], h => by
        simp [FieldAccess.structuralInputFieldsEqBool] at h
end

mutual
  private theorem structuralInputValueEqBool_refl :
      ∀ value,
        FieldAccess.structuralInputValueEqBool value value = true
    | .null => by
        simp [FieldAccess.structuralInputValueEqBool]
    | .int _value => by
        simp [FieldAccess.structuralInputValueEqBool]
    | .float _value => by
        simp [FieldAccess.structuralInputValueEqBool]
    | .string _value => by
        simp [FieldAccess.structuralInputValueEqBool]
    | .boolean _value => by
        simp [FieldAccess.structuralInputValueEqBool]
    | .enum _value => by
        simp [FieldAccess.structuralInputValueEqBool]
    | .variable _value => by
        simp [FieldAccess.structuralInputValueEqBool]
    | .list values => by
        simp [FieldAccess.structuralInputValueEqBool,
          structuralInputValuesEqBool_refl values]
    | .object fields => by
        simp [FieldAccess.structuralInputValueEqBool,
          structuralInputFieldsEqBool_refl fields]

  private theorem structuralInputValuesEqBool_refl :
      ∀ values,
        FieldAccess.structuralInputValuesEqBool values values = true
    | [] => by
        simp [FieldAccess.structuralInputValuesEqBool]
    | value :: rest => by
        simp [FieldAccess.structuralInputValuesEqBool,
          structuralInputValueEqBool_refl value,
          structuralInputValuesEqBool_refl rest]

  private theorem structuralInputFieldsEqBool_refl :
      ∀ fields,
        FieldAccess.structuralInputFieldsEqBool fields fields = true
    | [] => by
        simp [FieldAccess.structuralInputFieldsEqBool]
    | (name, value) :: rest => by
        simp [FieldAccess.structuralInputFieldsEqBool,
          structuralInputValueEqBool_refl value,
          structuralInputFieldsEqBool_refl rest]
end

mutual
  private theorem structuralInputValueEqBool_eq :
      ∀ left right,
        FieldAccess.structuralInputValueEqBool left right = true ->
          left = right
    | left, right, h => by
        cases left <;> cases right <;>
          simp [FieldAccess.structuralInputValueEqBool] at h
        all_goals
          first
          | rfl
          | subst_vars; rfl
          | exact congrArg InputValue.list
              (structuralInputValuesEqBool_eq _ _ h)
          | exact congrArg InputValue.object
              (structuralInputFieldsEqBool_eq _ _ h)

  private theorem structuralInputValuesEqBool_eq :
      ∀ left right,
        FieldAccess.structuralInputValuesEqBool left right = true ->
          left = right
    | [], [], _h => by
        rfl
    | left :: leftRest, right :: rightRest, h => by
        simp [FieldAccess.structuralInputValuesEqBool] at h
        have hhead := structuralInputValueEqBool_eq left right h.1
        have htail := structuralInputValuesEqBool_eq leftRest rightRest h.2
        subst right
        subst rightRest
        rfl
    | [], _ :: _, h
    | _ :: _, [], h => by
        simp [FieldAccess.structuralInputValuesEqBool] at h

  private theorem structuralInputFieldsEqBool_eq :
      ∀ left right,
        FieldAccess.structuralInputFieldsEqBool left right = true ->
          left = right
    | [], [], _h => by
        rfl
    | (leftName, leftValue) :: leftRest,
      (rightName, rightValue) :: rightRest, h => by
        simp [FieldAccess.structuralInputFieldsEqBool] at h
        have hname : leftName = rightName := h.1.1
        have hvalue := structuralInputValueEqBool_eq leftValue rightValue
          h.1.2
        have htail := structuralInputFieldsEqBool_eq leftRest rightRest h.2
        subst rightName
        subst rightValue
        subst rightRest
        rfl
    | [], _ :: _, h
    | _ :: _, [], h => by
        simp [FieldAccess.structuralInputFieldsEqBool] at h
end

private theorem structuralInputValueEqBool_trans
    {left middle right : InputValue} :
    FieldAccess.structuralInputValueEqBool left middle = true ->
    FieldAccess.structuralInputValueEqBool middle right = true ->
      FieldAccess.structuralInputValueEqBool left right = true := by
  intro hleft hright
  have hleftEq := structuralInputValueEqBool_eq left middle hleft
  have hrightEq := structuralInputValueEqBool_eq middle right hright
  subst middle
  subst right
  exact structuralInputValueEqBool_refl left

private theorem argumentEqBool_trans
    {left middle right : Argument} :
    FieldAccess.argumentEqBool left middle = true ->
    FieldAccess.argumentEqBool middle right = true ->
      FieldAccess.argumentEqBool left right = true := by
  intro hleft hright
  simp [FieldAccess.argumentEqBool,
    FieldAccess.canonicalInputValue] at hleft hright ⊢
  exact ⟨hleft.1.trans hright.1,
    structuralInputValueEqBool_trans hleft.2 hright.2⟩

private theorem argumentEqBool_symm
    {left right : Argument} :
    FieldAccess.argumentEqBool left right = true ->
      FieldAccess.argumentEqBool right left = true := by
  intro h
  simp [FieldAccess.argumentEqBool,
    FieldAccess.canonicalInputValue] at h ⊢
  exact ⟨h.1.symm, structuralInputValueEqBool_symm _ _ h.2⟩

private theorem argumentsEqBoolOrdered_trans :
    ∀ left middle right,
      FieldAccess.argumentsEqBoolOrdered left middle = true ->
      FieldAccess.argumentsEqBoolOrdered middle right = true ->
        FieldAccess.argumentsEqBoolOrdered left right = true
  | [], [], [], _hleft, _hright => by
      simp [FieldAccess.argumentsEqBoolOrdered]
  | leftHead :: leftRest, middleHead :: middleRest,
    rightHead :: rightRest, hleft, hright => by
      simp [FieldAccess.argumentsEqBoolOrdered] at hleft hright ⊢
      exact ⟨argumentEqBool_trans hleft.1 hright.1,
        argumentsEqBoolOrdered_trans leftRest middleRest rightRest
          hleft.2 hright.2⟩
  | [], [], _ :: _, _hleft, hright => by
      simp [FieldAccess.argumentsEqBoolOrdered] at hright
  | [], _ :: _, _, hleft, _hright => by
      simp [FieldAccess.argumentsEqBoolOrdered] at hleft
  | _ :: _, [], _, hleft, _hright => by
      simp [FieldAccess.argumentsEqBoolOrdered] at hleft
  | _ :: _, _ :: _, [], _hleft, hright => by
      simp [FieldAccess.argumentsEqBoolOrdered] at hright

private theorem argumentsEqBoolOrdered_symm :
    ∀ {left right},
      FieldAccess.argumentsEqBoolOrdered left right = true ->
        FieldAccess.argumentsEqBoolOrdered right left = true
  | [], [], _h => by
      simp [FieldAccess.argumentsEqBoolOrdered]
  | leftHead :: leftRest, rightHead :: rightRest, h => by
      simp [FieldAccess.argumentsEqBoolOrdered] at h ⊢
      exact ⟨argumentEqBool_symm h.1,
        argumentsEqBoolOrdered_symm h.2⟩
  | [], _ :: _, h
  | _ :: _, [], h => by
      simp [FieldAccess.argumentsEqBoolOrdered] at h

private theorem argumentsEqBool_trans
    {left middle right : List Argument} :
    FieldAccess.argumentsEqBool left middle = true ->
    FieldAccess.argumentsEqBool middle right = true ->
      FieldAccess.argumentsEqBool left right = true := by
  intro hleft hright
  unfold FieldAccess.argumentsEqBool at hleft hright ⊢
  exact argumentsEqBoolOrdered_trans _ _ _ hleft hright

private theorem argumentsEqBool_symm
    {left right : List Argument} :
    FieldAccess.argumentsEqBool left right = true ->
      FieldAccess.argumentsEqBool right left = true := by
  intro h
  unfold FieldAccess.argumentsEqBool at h ⊢
  exact argumentsEqBoolOrdered_symm h

private theorem fieldAccess_eqBool_trans
    {left middle right : FieldAccess} :
    FieldAccess.eqBool left middle = true ->
    FieldAccess.eqBool middle right = true ->
      FieldAccess.eqBool left right = true := by
  intro hleft hright
  simp [FieldAccess.eqBool] at hleft hright ⊢
  exact ⟨hleft.1.trans hright.1,
    argumentsEqBool_trans hleft.2 hright.2⟩

private theorem fieldAccess_eqBool_symm
    {left right : FieldAccess} :
    FieldAccess.eqBool left right = true ->
      FieldAccess.eqBool right left = true := by
  intro h
  simp [FieldAccess.eqBool] at h ⊢
  exact ⟨h.1.symm, argumentsEqBool_symm h.2⟩

private theorem pathStep_eqBool_trans
    {left middle right : PathStep} :
    PathStep.eqBool left middle = true ->
    PathStep.eqBool middle right = true ->
      PathStep.eqBool left right = true := by
  intro hleft hright
  cases left <;> cases middle <;> cases right <;>
    simp [PathStep.eqBool] at hleft hright ⊢
  · exact fieldAccess_eqBool_trans hleft hright
  · exact hleft.trans hright

private theorem pathStep_eqBool_symm
    {left right : PathStep} :
    PathStep.eqBool left right = true ->
      PathStep.eqBool right left = true := by
  intro h
  cases left <;> cases right <;>
    simp [PathStep.eqBool] at h ⊢
  · exact fieldAccess_eqBool_symm h
  · exact h.symm

private theorem objectPath_eqBool_symm :
    ∀ {left right : ObjectPath},
      ObjectPath.eqBool left right = true ->
        ObjectPath.eqBool right left = true
  | [], [], _h => by
      simp [ObjectPath.eqBool]
  | leftHead :: leftRest, rightHead :: rightRest, h => by
      simp [ObjectPath.eqBool] at h ⊢
      exact ⟨pathStep_eqBool_symm h.1,
        objectPath_eqBool_symm h.2⟩
  | [], _ :: _, h
  | _ :: _, [], h => by
      simp [ObjectPath.eqBool] at h

private theorem objectPath_eqBool_trans :
    ∀ left middle right : ObjectPath,
      ObjectPath.eqBool left middle = true ->
      ObjectPath.eqBool middle right = true ->
        ObjectPath.eqBool left right = true
  | [], [], [], _hleft, _hright => by
      simp [ObjectPath.eqBool]
  | leftHead :: leftRest, middleHead :: middleRest,
    rightHead :: rightRest, hleft, hright => by
      simp [ObjectPath.eqBool] at hleft hright ⊢
      exact ⟨pathStep_eqBool_trans hleft.1 hright.1,
        objectPath_eqBool_trans leftRest middleRest rightRest hleft.2 hright.2⟩
  | [], [], _ :: _, _hleft, hright => by
      simp [ObjectPath.eqBool] at hright
  | [], _ :: _, _, hleft, _hright => by
      simp [ObjectPath.eqBool] at hleft
  | _ :: _, [], _, hleft, _hright => by
      simp [ObjectPath.eqBool] at hleft
  | _ :: _, _ :: _, [], _hleft, hright => by
      simp [ObjectPath.eqBool] at hright

private theorem lookupNodeIn?_eq_of_objectPath_eqBool
    (path otherPath : ObjectPath) :
    ObjectPath.eqBool path otherPath = true ->
      ∀ nodes,
        lookupNodeIn? path nodes =
          lookupNodeIn? otherPath nodes
  | hpath, [] => by
      simp [lookupNodeIn?]
  | hpath, node :: rest => by
      by_cases hnodePath :
          ObjectPath.eqBool node.path path = true
      · have hnodeOther :
            ObjectPath.eqBool node.path otherPath = true :=
          objectPath_eqBool_trans node.path path otherPath hnodePath hpath
        simp [lookupNodeIn?, hnodePath, hnodeOther]
      · have hnodePathFalse :
            ObjectPath.eqBool node.path path = false := by
          cases hmatch :
              ObjectPath.eqBool node.path path
          · rfl
          · exact False.elim (hnodePath hmatch)
        have hotherPath :
            ObjectPath.eqBool otherPath path = true :=
          objectPath_eqBool_symm hpath
        have hnodeOtherFalse :
            ObjectPath.eqBool node.path otherPath = false := by
          cases hmatch :
              ObjectPath.eqBool node.path otherPath
          · rfl
          · have hnodePathTrue :
                ObjectPath.eqBool node.path path = true :=
              objectPath_eqBool_trans node.path otherPath path hmatch
                hotherPath
            exact False.elim (by
              rw [hnodePathFalse] at hnodePathTrue
              cases hnodePathTrue)
        simp [lookupNodeIn?, hnodePathFalse,
          hnodeOtherFalse,
          lookupNodeIn?_eq_of_objectPath_eqBool path otherPath hpath rest]

private theorem lookupNode?_eq_of_objectPath_eqBool
    (store : DataModel.Store) {path otherPath : ObjectPath} :
    ObjectPath.eqBool path otherPath = true ->
      store.lookupNode? path = store.lookupNode? otherPath := by
  intro hpath
  exact lookupNodeIn?_eq_of_objectPath_eqBool path otherPath hpath
    store.allNodes

private theorem edge_targets_include_of_lookupField
    (schema : Schema) (store : DataModel.Store)
    (runtimeType : Name) (identity : ObjectPath)
    (fieldName : Name) (arguments : List Argument)
    (fieldDefinition : FieldDefinition) (node : ObjectNode) :
    store.wellTyped schema ->
    store.lookupNode? identity = some node ->
    node.typeName = runtimeType ->
    schema.lookupField runtimeType fieldName = some fieldDefinition ->
    (let field := fieldAccess fieldName arguments
     ∀ edge, edge ∈ store.edges ->
      edge.matchesField identity field = true ->
        schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
          edge.targetType = true) := by
  intro hstore hnode hnodeType hlookup field edge hedge hmatches
  have hedgeWell := hstore.2.2.2.2.1 edge hedge
  rcases hedgeWell with
    ⟨sourceNode, implementationDefinition, targetNode, hsourceLookup,
      himplementationLookup, _hpossible, _harguments, _hlistLike,
      htarget, _htargetLookup, _htargetType⟩
  have hsourcePath :=
    objectEdge_matchesField_sourcePath edge identity field hmatches
  have hlookupEq :
      store.lookupNode? edge.sourcePath = store.lookupNode? identity :=
    lookupNode?_eq_of_objectPath_eqBool store hsourcePath
  rw [hlookupEq, hnode] at hsourceLookup
  cases hsourceLookup
  have hfieldName :
      edge.field.name = fieldName := by
    have hfield := objectEdge_matchesField_fieldName edge identity field
      hmatches
    simpa [field, fieldAccess] using hfield
  have himplementationLookup' :
      schema.lookupField runtimeType fieldName =
        some implementationDefinition := by
    simpa [hnodeType, hfieldName] using himplementationLookup
  rw [hlookup] at himplementationLookup'
  cases himplementationLookup'
  exact List.contains_iff_mem.mpr htarget

private theorem resolveValue_objectsInclude_of_runtime_lookupField
    (schema : Schema) (store : DataModel.Store)
    (runtimeType : Name) (identity : ObjectPath)
    (fieldName : Name) (arguments : List Argument)
    (fieldDefinition : FieldDefinition) :
    store.wellTyped schema ->
    schema.lookupField runtimeType fieldName = some fieldDefinition ->
      storeValueObjectsInclude schema fieldDefinition.outputType.namedType
        (store.resolveValue schema fieldName arguments
          (.object runtimeType identity)) := by
  intro hstore hlookup
  cases hnode : store.lookupNode? identity with
  | none =>
      simp [resolveValue, hnode, storeValueObjectsInclude]
  | some node =>
      by_cases htype : (node.typeName == runtimeType) = true
      · have hnodeType : node.typeName = runtimeType :=
          beq_iff_eq.mp htype
        exact
          resolveValue_objectsInclude_of_lookupField_and_edges schema store
            runtimeType identity fieldName arguments fieldDefinition hstore
            hlookup
            (edge_targets_include_of_lookupField schema store runtimeType
              identity fieldName arguments fieldDefinition node hstore hnode
              hnodeType hlookup)
      · have htypeFalse : (node.typeName == runtimeType) = false := by
          cases hmatch : node.typeName == runtimeType
          · rfl
          · exact False.elim (htype hmatch)
        simp [resolveValue, hnode, htypeFalse,
          storeValueObjectsInclude]

private theorem resolveValue_objectsInclude_of_static_lookupField
    (schema : Schema) (store : DataModel.Store)
    (parentType runtimeType : Name) (identity : ObjectPath)
    (fieldName : Name) (arguments : List Argument)
    (fieldDefinition : FieldDefinition) :
    SchemaWellFormedness.schemaWellFormed schema ->
    store.wellTyped schema ->
    schema.typeIncludesObjectBool parentType runtimeType = true ->
    schema.lookupField parentType fieldName = some fieldDefinition ->
      storeValueObjectsInclude schema fieldDefinition.outputType.namedType
        (store.resolveValue schema fieldName arguments
          (.object runtimeType identity)) := by
  intro hschema hstore hinclude hlookup
  have hpossible : runtimeType ∈ schema.getPossibleTypes parentType :=
    List.contains_iff_mem.mp hinclude
  rcases
    SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_exists
      hschema hpossible hlookup with
    ⟨implementationDefinition, himplementationLookup⟩
  have himplementation :=
    resolveValue_objectsInclude_of_runtime_lookupField schema store
      runtimeType identity fieldName arguments implementationDefinition
      hstore himplementationLookup
  have hsubtype :
      schema.outputTypeSubtype implementationDefinition.outputType
        fieldDefinition.outputType :=
    SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
      hschema hpossible hlookup himplementationLookup
  exact storeValueObjectsInclude_mono schema
    (fun objectType hobject =>
      GraphQL.typeIncludesObjectBool_of_outputTypeSubtype_namedType schema
        hsubtype hobject)
    (store.resolveValue schema fieldName arguments
      (.object runtimeType identity))
    himplementation

theorem resolve_objectsInclude_of_static_lookupField
    (schema : Schema) (store : DataModel.Store)
    (parentType runtimeType : Name) (identity : ObjectPath)
    (fieldName : Name) (arguments : List Argument)
    (fieldDefinition : FieldDefinition) :
    SchemaWellFormedness.schemaWellFormed schema ->
    store.wellTyped schema ->
    schema.typeIncludesObjectBool parentType runtimeType = true ->
    schema.lookupField parentType fieldName = some fieldDefinition ->
      executionValueObjectsInclude schema fieldDefinition.outputType.namedType
        (store.resolve schema fieldName arguments
          (.object runtimeType identity)) := by
  intro hschema hstore hinclude hlookup
  simp [resolve]
  exact storeValueObjectsInclude_toExecutionValue schema
    fieldDefinition.outputType.namedType
    (store.resolveValue schema fieldName arguments
      (.object runtimeType identity))
    (resolveValue_objectsInclude_of_static_lookupField schema store
      parentType runtimeType identity fieldName arguments fieldDefinition
      hschema hstore hinclude hlookup)

theorem resolvers_parentType_insensitive
    (schema : Schema) (store : DataModel.Store)
    (leftParentType rightParentType fieldName : Name)
    (arguments : List Argument)
    (source : Execution.Value ObjectPath) :
    (store.resolvers schema).resolve leftParentType fieldName arguments source =
      (store.resolvers schema).resolve rightParentType fieldName arguments
        source := by
  rfl

end Store

end DataModel

end GraphQL
