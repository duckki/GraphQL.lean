import GraphQL.NormalForm.GroundTypeNormalization.Normality
import GraphQL.NormalForm.Shared.SemanticReadiness
import GraphQL.NormalForm.Shared.FieldMergeLookup

/-!
Basic validity support facts for ground-type normalization.
-/
namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

mutual
  theorem inputValue_structuralEquivalent_refl :
      ∀ value, InputValue.structuralEquivalent value value
    | .null => by simp [InputValue.structuralEquivalent]
    | .int _ => by simp [InputValue.structuralEquivalent]
    | .float _ => by simp [InputValue.structuralEquivalent]
    | .string _ => by simp [InputValue.structuralEquivalent]
    | .boolean _ => by simp [InputValue.structuralEquivalent]
    | .enum _ => by simp [InputValue.structuralEquivalent]
    | .variable _ => by simp [InputValue.structuralEquivalent]
    | .list values => by
        simp [InputValue.structuralEquivalent,
          inputValues_structuralEquivalent_refl values]
    | .object fields => by
        simp [InputValue.structuralEquivalent,
          inputObjectFields_structuralEquivalent_refl fields]

  theorem inputValues_structuralEquivalent_refl :
      ∀ values, InputValue.structuralValuesEquivalent values values
    | [] => by simp [InputValue.structuralValuesEquivalent]
    | value :: rest => by
        simp [InputValue.structuralValuesEquivalent,
          inputValue_structuralEquivalent_refl value,
          inputValues_structuralEquivalent_refl rest]

  theorem inputObjectFields_structuralEquivalent_refl :
      ∀ fields, InputValue.structuralObjectFieldsEquivalent fields fields
    | [] => by simp [InputValue.structuralObjectFieldsEquivalent]
    | (name, value) :: rest => by
        simp [InputValue.structuralObjectFieldsEquivalent,
          inputValue_structuralEquivalent_refl value,
          inputObjectFields_structuralEquivalent_refl rest]
end

theorem inputValue_equivalent_refl (value : InputValue) :
    value.equivalent value := by
  exact inputValue_structuralEquivalent_refl value.canonical

theorem argument_equivalent_refl (argument : Argument) :
    argument.equivalent argument := by
  exact ⟨rfl, inputValue_equivalent_refl argument.value⟩

theorem argumentsEquivalent_refl (arguments : List Argument) :
    Argument.argumentsEquivalent arguments arguments := by
  constructor
  · intro argument hargument
    exact ⟨argument, hargument, argument_equivalent_refl argument⟩
  · intro argument hargument
    exact ⟨argument, hargument, argument_equivalent_refl argument⟩

theorem objectType_isCompositeType
    {schema : Schema} {typeName : Name} :
    schema.objectType typeName -> schema.isCompositeType typeName := by
  intro hobject
  rcases hobject with ⟨objectType, hlookup⟩
  exact ⟨.object objectType, hlookup, by simp [TypeDefinition.isCompositeType]⟩

theorem leafTypeNameBool_eq_true_isLeafType
    (schema : Schema) {typeName : Name} :
    leafTypeNameBool schema typeName = true ->
      schema.isLeafType typeName := by
  intro hleaf
  unfold leafTypeNameBool at hleaf
  cases hlookup : schema.lookupType typeName with
  | none =>
      simp [hlookup] at hleaf
  | some typeDefinition =>
      cases typeDefinition with
      | builtinScalar scalar =>
          exact ⟨.builtinScalar scalar, hlookup,
            by simp [TypeDefinition.isLeafType]⟩
      | customScalar scalar =>
          exact ⟨.customScalar scalar, hlookup,
            by simp [TypeDefinition.isLeafType]⟩
      | object objectType =>
          simp [hlookup] at hleaf
      | interface interfaceType =>
          simp [hlookup] at hleaf
      | union unionType =>
          simp [hlookup] at hleaf
      | enum enumType =>
          exact ⟨.enum enumType, hlookup,
            by simp [TypeDefinition.isLeafType]⟩
      | inputObject inputObjectType =>
          simp [hlookup] at hleaf

theorem leafTypeNameBool_eq_true_of_isLeafType
    (schema : Schema) {typeName : Name} :
    schema.isLeafType typeName ->
      leafTypeNameBool schema typeName = true := by
  intro hleaf
  rcases hleaf with ⟨typeDefinition, hlookup, hleafDefinition⟩
  cases typeDefinition with
  | builtinScalar scalar =>
      simp [leafTypeNameBool, hlookup]
  | customScalar scalar =>
      simp [leafTypeNameBool, hlookup]
  | object objectType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition
  | interface interfaceType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition
  | union unionType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition
  | enum enumType =>
      simp [leafTypeNameBool, hlookup]
  | inputObject inputObjectType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition

theorem isLeafType_not_isCompositeType
    {schema : Schema} {typeName : Name} :
    schema.isLeafType typeName -> schema.isCompositeType typeName -> False := by
  intro hleaf hcomposite
  rcases hleaf with ⟨leafDefinition, hleafLookup, hleafType⟩
  rcases hcomposite with
    ⟨compositeDefinition, hcompositeLookup, hcompositeType⟩
  rw [hleafLookup] at hcompositeLookup
  cases hcompositeLookup
  cases leafDefinition <;>
    simp [TypeDefinition.isLeafType, TypeDefinition.isCompositeType]
      at hleafType hcompositeType

theorem leafTypeNameBool_eq_false_of_isCompositeType
    (schema : Schema) {typeName : Name} :
    schema.isCompositeType typeName ->
      leafTypeNameBool schema typeName = false := by
  intro hcomposite
  cases hleaf : leafTypeNameBool schema typeName
  · rfl
  · exact False.elim
      (isLeafType_not_isCompositeType
        (leafTypeNameBool_eq_true_isLeafType schema hleaf)
        hcomposite)

theorem objectTypeNameBool_eq_false_of_isLeafType
    (schema : Schema) {typeName : Name} :
    schema.isLeafType typeName ->
      objectTypeNameBool schema typeName = false := by
  intro hleaf
  rcases hleaf with ⟨typeDefinition, hlookup, hleafDefinition⟩
  cases typeDefinition with
  | builtinScalar scalar =>
      simp [objectTypeNameBool, hlookup]
  | customScalar scalar =>
      simp [objectTypeNameBool, hlookup]
  | object objectType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition
  | interface interfaceType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition
  | union unionType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition
  | enum enumType =>
      simp [objectTypeNameBool, hlookup]
  | inputObject inputObjectType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition

theorem possibleTypes_eq_nil_of_leafTypeNameBool
    (schema : Schema) {typeName : Name} :
    leafTypeNameBool schema typeName = true ->
      schema.getPossibleTypes typeName = [] := by
  intro hleaf
  exact possibleTypes_eq_nil_of_isLeafType schema
    (leafTypeNameBool_eq_true_isLeafType schema hleaf)

theorem object_typeIncludesObject_self
    (schema : Schema) {typeName : Name} :
    schema.objectType typeName ->
      schema.typeIncludesObject typeName typeName := by
  intro hobject
  exact List.contains_iff_mem.mp
    (object_typeIncludesObjectBool_self schema hobject)

theorem typesOverlap_possible_object
    (schema : Schema) {parentType objectType : Name} :
    objectType ∈ schema.getPossibleTypes parentType ->
    schema.objectType objectType ->
      schema.typesOverlap parentType objectType := by
  intro hpossible hobject
  exact ⟨objectType, hpossible,
    object_typeIncludesObject_self schema hobject⟩

theorem typesOverlapBool_eq_true_of_typesOverlap
    (schema : Schema) {left right : Name} :
    schema.typesOverlap left right ->
      schema.typesOverlapBool left right = true := by
  intro hoverlap
  rcases hoverlap with ⟨objectName, hleft, hright⟩
  unfold Schema.typesOverlapBool
  rw [List.any_eq_true]
  exact ⟨objectName, hleft, List.contains_iff_mem.mpr hright⟩

theorem possibleTypes_ne_nil_left_of_typesOverlap
    (schema : Schema) {left right : Name} :
    schema.typesOverlap left right ->
      schema.getPossibleTypes left ≠ [] := by
  intro hoverlap hnil
  rcases hoverlap with ⟨objectName, hleft, _hright⟩
  unfold Schema.typeIncludesObject at hleft
  rw [hnil] at hleft
  cases hleft

theorem possibleTypes_ne_nil_right_of_typesOverlap
    (schema : Schema) {left right : Name} :
    schema.typesOverlap left right ->
      schema.getPossibleTypes right ≠ [] := by
  intro hoverlap hnil
  rcases hoverlap with ⟨objectName, _hleft, hright⟩
  unfold Schema.typeIncludesObject at hright
  rw [hnil] at hright
  cases hright

theorem selectionSetImplementationValidInScope_nil
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) :
    Validation.selectionSetImplementationValidInScope schema
      variableDefinitions parentType [] := by
  simp [Validation.selectionSetImplementationValidInScope]

theorem selectionSetImplementationValidInScope_cons
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selection : Selection}
    {selectionSet : List Selection} :
    Validation.selectionImplementationValid schema variableDefinitions
      parentType selection ->
    Validation.selectionSetImplementationValidInScope schema variableDefinitions
      parentType selectionSet ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions parentType (selection :: selectionSet) := by
  intro hselection hselectionSet
  simp [Validation.selectionSetImplementationValidInScope, hselection,
    hselectionSet]

theorem selectionSetImplementationValidInScope_head
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selection : Selection}
    {selectionSet : List Selection} :
    Validation.selectionSetImplementationValidInScope schema
      variableDefinitions parentType (selection :: selectionSet) ->
      Validation.selectionImplementationValid schema variableDefinitions
        parentType selection := by
  intro hvalid
  simpa [Validation.selectionSetImplementationValidInScope] using hvalid.1

theorem selectionSetImplementationValidInScope_tail
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selection : Selection}
    {selectionSet : List Selection} :
    Validation.selectionSetImplementationValidInScope schema
      variableDefinitions parentType (selection :: selectionSet) ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions parentType selectionSet := by
  intro hvalid
  simpa [Validation.selectionSetImplementationValidInScope] using hvalid.2

theorem selectionSetImplementationValidInScope_append
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection} :
    Validation.selectionSetImplementationValidInScope schema
      variableDefinitions parentType left ->
    Validation.selectionSetImplementationValidInScope schema
      variableDefinitions parentType right ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions parentType (left ++ right) := by
  intro hleft hright
  induction left with
  | nil =>
      simpa using hright
  | cons selection rest ih =>
      have hhead :=
        selectionSetImplementationValidInScope_head hleft
      have htail :=
        selectionSetImplementationValidInScope_tail hleft
      simp [Validation.selectionSetImplementationValidInScope]
      exact ⟨hhead, ih htail⟩

theorem selectionSetImplementationValidInScope_append_left
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection} :
    Validation.selectionSetImplementationValidInScope schema
      variableDefinitions parentType (left ++ right) ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions parentType left := by
  intro hvalid
  induction left with
  | nil =>
      exact selectionSetImplementationValidInScope_nil schema
        variableDefinitions parentType
  | cons selection rest ih =>
      simp [Validation.selectionSetImplementationValidInScope] at hvalid ⊢
      exact ⟨hvalid.1, ih hvalid.2⟩

theorem selectionSetImplementationValidInScope_append_right
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection} :
    Validation.selectionSetImplementationValidInScope schema
      variableDefinitions parentType (left ++ right) ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions parentType right := by
  intro hvalid
  induction left with
  | nil =>
      simpa using hvalid
  | cons selection rest ih =>
      exact ih (selectionSetImplementationValidInScope_tail hvalid)

theorem selectionSetImplementationValidInScope_withoutFieldsWithResponseName
    (schema : Schema) (responseName : Name) :
    ∀ variableDefinitions parentType selectionSet,
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions parentType selectionSet ->
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions parentType
          (withoutFieldsWithResponseName schema responseName selectionSet)
  | _variableDefinitions, _parentType, [], _hvalid => by
      simp [withoutFieldsWithResponseName,
        Validation.selectionSetImplementationValidInScope]
  | variableDefinitions, parentType, selection :: rest, hvalid => by
      have hhead :=
        selectionSetImplementationValidInScope_head hvalid
      have htail :=
        selectionSetImplementationValidInScope_tail hvalid
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [withoutFieldsWithResponseName, hname]
            exact
              selectionSetImplementationValidInScope_withoutFieldsWithResponseName
                schema responseName variableDefinitions parentType rest htail
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldsWithResponseName, hfalse,
              Validation.selectionSetImplementationValidInScope]
            exact ⟨hhead,
              selectionSetImplementationValidInScope_withoutFieldsWithResponseName
                schema responseName variableDefinitions parentType rest htail⟩
      | inlineFragment typeCondition directives selectionSet =>
          simp [withoutFieldsWithResponseName,
            Validation.selectionSetImplementationValidInScope]
          constructor
          · cases typeCondition with
            | none =>
                simpa [Validation.selectionImplementationValid] using
                  selectionSetImplementationValidInScope_withoutFieldsWithResponseName
                    schema responseName variableDefinitions parentType
                    selectionSet hhead
            | some typeCondition =>
                intro hoverlap
                have hfragment :
                    Validation.selectionSetImplementationValidInScope schema
                      variableDefinitions typeCondition selectionSet
                    ∧ ∀ objectType,
                      objectType ∈ schema.getPossibleTypes typeCondition ->
                        Validation.selectionSetImplementationValidInScope
                          schema variableDefinitions objectType
                          selectionSet := by
                  simpa [Validation.selectionImplementationValid] using
                    hhead hoverlap
                exact ⟨
                  selectionSetImplementationValidInScope_withoutFieldsWithResponseName
                    schema responseName variableDefinitions typeCondition
                    selectionSet hfragment.1,
                  fun objectType hobjectType =>
                    selectionSetImplementationValidInScope_withoutFieldsWithResponseName
                      schema responseName variableDefinitions objectType
                      selectionSet (hfragment.2 objectType hobjectType)⟩
          · exact
              selectionSetImplementationValidInScope_withoutFieldsWithResponseName
                schema responseName variableDefinitions parentType rest htail

theorem selectionSetImplementationValidInScope_mergeSelectionSets_of_subselections
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} :
    ∀ selections,
      (∀ selection, selection ∈ selections ->
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions parentType selection.subselections) ->
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions parentType (mergeSelectionSets selections)
  | [], _hvalid => by
      simp [mergeSelectionSets,
        Validation.selectionSetImplementationValidInScope]
  | selection :: rest, hvalid => by
      simp [mergeSelectionSets]
      apply selectionSetImplementationValidInScope_append
      · exact hvalid selection (by simp)
      · exact
          selectionSetImplementationValidInScope_mergeSelectionSets_of_subselections
            rest (by
              intro candidate hcandidate
              exact hvalid candidate (by simp [hcandidate]))

theorem selectionSetImplementationValidInScope_mergeSelectionSets_of_field_subselections
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName : Name}
    (selections : List Selection) :
    (∀ selection, selection ∈ selections ->
      ∃ fieldName arguments directives subselections,
        selection =
          Selection.field responseName fieldName arguments directives
            subselections) ->
    (∀ fieldName arguments directives subselections,
      Selection.field responseName fieldName arguments directives
          subselections ∈ selections ->
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions parentType subselections) ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions parentType (mergeSelectionSets selections) := by
  intro hshape hfields
  apply selectionSetImplementationValidInScope_mergeSelectionSets_of_subselections
  intro selection hselection
  rcases hshape selection hselection with
    ⟨fieldName, arguments, directives, subselections, hselectionShape⟩
  subst selection
  simpa [Selection.subselections] using
    hfields fieldName arguments directives subselections hselection

theorem selectionSetImplementationValidInScope_mergeSelectionSets_validFieldsWithResponseName
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName childType : Name}
    (selectionSet : List Selection) :
    (∀ fieldName arguments directives subselections,
      Selection.field responseName fieldName arguments directives subselections
        ∈ validFieldsWithResponseName schema parentType responseName
          selectionSet ->
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions childType subselections) ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions childType
        (mergeSelectionSets
          (validFieldsWithResponseName schema parentType responseName
            selectionSet)) := by
  intro hfields
  apply selectionSetImplementationValidInScope_mergeSelectionSets_of_field_subselections
  · intro selection hselection
    exact validFieldsWithResponseName_mem_field schema parentType responseName
      selectionSet selection hselection
  · intro fieldName arguments directives subselections hselection
    exact hfields fieldName arguments directives subselections hselection

theorem selectionSetValid_of_allFields_implementationValidInScope
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) :
    ∀ selectionSet,
      selectionsAllFields selectionSet ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions parentType selectionSet ->
        Validation.selectionSetValid schema variableDefinitions parentType
          selectionSet
  | [], _hallFields, _himplementation => by
      simp [Validation.selectionSetValid]
  | selection :: rest, hallFields, himplementation => by
      have hheadField : Selection.isField selection :=
        hallFields selection (by simp)
      have htailAllFields : selectionsAllFields rest := by
        intro candidate hcandidate
        exact hallFields candidate
          (List.mem_cons_of_mem selection hcandidate)
      have hheadImplementation :
          Validation.selectionImplementationValid schema variableDefinitions
            parentType selection :=
        selectionSetImplementationValidInScope_head himplementation
      have htailImplementation :
          Validation.selectionSetImplementationValidInScope schema
            variableDefinitions parentType rest :=
        selectionSetImplementationValidInScope_tail himplementation
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          have hheadValid :
              Validation.selectionValid schema variableDefinitions parentType
                (Selection.field responseName fieldName arguments directives
                  selectionSet) := by
            simpa [Validation.selectionImplementationValid] using
              hheadImplementation.1
          have htailValid :
              ∀ candidate, candidate ∈ rest ->
                Validation.selectionValid schema variableDefinitions
                  parentType candidate := by
            simpa [Validation.selectionSetValid] using
              selectionSetValid_of_allFields_implementationValidInScope
                schema variableDefinitions parentType rest htailAllFields
                htailImplementation
          simp [Validation.selectionSetValid]
          exact ⟨hheadValid, htailValid⟩
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hheadField


end GroundTypeNormalization

end NormalForm

end GraphQL
