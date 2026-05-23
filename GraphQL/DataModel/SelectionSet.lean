import GraphQL.DataModel

/-!
Spec reference: GraphQL September 2025.
- 6.3.2 `CollectFields` and 6.3.3 `ExecuteCollectedFields`: selection-set proof
  cases for multiple response names in the scoped data model.
- Fidelity note: this module stays inside the same query-only, already-coerced,
  data-only execution fragment as `GraphQL.DataModel`.
-/
namespace GraphQL

namespace DataModel

structure LeafField where
  responseName : Name
  fieldName : Name
  arguments : List Argument
deriving Repr

namespace LeafField

def toSelection (field : LeafField) : Semantic.Selection :=
  .field field.responseName field.fieldName field.arguments [] []

def toSelectionSet (fields : List LeafField) : List Semantic.Selection :=
  fields.map toSelection

def responseNames (fields : List LeafField) : List Name :=
  fields.map LeafField.responseName

def responseNamesNodup (fields : List LeafField) : Prop :=
  (responseNames fields).Nodup

@[simp]
theorem toSelection_responseName? (field : LeafField) :
    field.toSelection.responseName? = some field.responseName := by
  cases field
  rfl

@[simp]
theorem toSelection_subselections (field : LeafField) :
    field.toSelection.subselections = [] := by
  cases field
  rfl

@[simp]
theorem toSelection_size (field : LeafField) :
    field.toSelection.size = 1 := by
  cases field
  simp [toSelection, Semantic.Selection.size, Semantic.SelectionSet.size]

theorem toSelectionSet_size (fields : List LeafField) :
    Semantic.SelectionSet.size (toSelectionSet fields) = fields.length := by
  induction fields with
  | nil =>
      simp [toSelectionSet, Semantic.SelectionSet.size]
  | cons field rest ih =>
      have ih' :
          Semantic.SelectionSet.size (List.map toSelection rest) = rest.length := by
        simpa [toSelectionSet] using ih
      simp [toSelectionSet, Semantic.SelectionSet.size, ih', Nat.add_comm]

theorem filterMap_responseName_toSelectionSet (fields : List LeafField) :
    ((toSelectionSet fields).filterMap Semantic.Selection.responseName?)
      = responseNames fields := by
  induction fields with
  | nil =>
      simp [toSelectionSet, responseNames]
  | cons field rest ih =>
      have ih' :
          (List.map toSelection rest).filterMap Semantic.Selection.responseName?
            = List.map LeafField.responseName rest := by
        simpa [toSelectionSet, responseNames] using ih
      simp [toSelectionSet, responseNames, ih']

theorem normalForm_responseNamesNodup (fields : List LeafField) :
    NormalForm.responseNamesNodup (toSelectionSet fields)
      ↔ responseNamesNodup fields := by
  simp [NormalForm.responseNamesNodup, responseNamesNodup,
    filterMap_responseName_toSelectionSet]

theorem selectionsAllFields_toSelectionSet (fields : List LeafField) :
    NormalForm.selectionsAllFields (toSelectionSet fields) := by
  intro selection hselection
  simp [toSelectionSet] at hselection
  rcases hselection with ⟨field, _hfield, rfl⟩
  cases field
  simp [toSelection, Semantic.Selection.isField]

theorem fieldsWithResponseName_toSelectionSet_notMem
    (responseName : Name) (fields : List LeafField) :
    responseName ∉ responseNames fields ->
      Semantic.SelectionSet.fieldsWithResponseName responseName
        (toSelectionSet fields) = [] := by
  intro hnotMem
  induction fields with
  | nil =>
      simp [toSelectionSet, Semantic.SelectionSet.fieldsWithResponseName]
  | cons field rest ih =>
      have hfield : field.responseName ≠ responseName := by
        intro hsame
        apply hnotMem
        simp [responseNames, hsame]
      have hfieldBool : (field.responseName == responseName) = false := by
        by_cases hsame : field.responseName = responseName
        · exact False.elim (hfield hsame)
        · simp [hsame]
      have hrest : responseName ∉ responseNames rest := by
        intro hmem
        apply hnotMem
        simp [responseNames]
        right
        simpa [responseNames] using hmem
      let responseNameMatches : Semantic.Selection -> Bool := fun selection =>
        match selection.responseName? with
        | some name => name == responseName
        | none => false
      have hhead :
          ¬ responseNameMatches (toSelection field) = true := by
        simp [responseNameMatches, toSelection, Semantic.Selection.responseName?,
          hfieldBool]
      have htail : List.filter responseNameMatches (List.map toSelection rest) = [] := by
        simpa [toSelectionSet, Semantic.SelectionSet.fieldsWithResponseName,
          responseNameMatches] using ih hrest
      rw [toSelectionSet, Semantic.SelectionSet.fieldsWithResponseName]
      simp only [List.map_cons]
      change List.filter responseNameMatches (toSelection field :: List.map toSelection rest)
        = []
      rw [List.filter_cons_of_neg hhead, htail]

theorem fieldsWithResponseName_toSelectionSet_cons_self
    (field : LeafField) (rest : List LeafField) :
    field.responseName ∉ responseNames rest ->
      Semantic.SelectionSet.fieldsWithResponseName field.responseName
        (toSelectionSet (field :: rest)) = [field.toSelection] := by
  intro hnotMem
  let responseNameMatches : Semantic.Selection -> Bool := fun selection =>
    match selection.responseName? with
    | some name => name == field.responseName
    | none => false
  have hhead : responseNameMatches (toSelection field) = true := by
    simp [responseNameMatches, toSelection, Semantic.Selection.responseName?]
  have htail : List.filter responseNameMatches (List.map toSelection rest) = [] := by
    simpa [toSelectionSet, Semantic.SelectionSet.fieldsWithResponseName,
      responseNameMatches] using
      fieldsWithResponseName_toSelectionSet_notMem field.responseName rest hnotMem
  rw [toSelectionSet, Semantic.SelectionSet.fieldsWithResponseName]
  simp only [List.map_cons]
  change List.filter responseNameMatches (toSelection field :: List.map toSelection rest)
    = [toSelection field]
  rw [List.filter_cons_of_pos hhead, htail]

theorem withoutFieldsWithResponseName_toSelectionSet_notMem
    (responseName : Name) (fields : List LeafField) :
    responseName ∉ responseNames fields ->
      Semantic.SelectionSet.withoutFieldsWithResponseName responseName
        (toSelectionSet fields) = toSelectionSet fields := by
  intro hnotMem
  induction fields with
  | nil =>
      simp [toSelectionSet, Semantic.SelectionSet.withoutFieldsWithResponseName]
  | cons field rest ih =>
      have hfield : field.responseName ≠ responseName := by
        intro hsame
        apply hnotMem
        simp [responseNames, hsame]
      have hfieldBool : (field.responseName == responseName) = false := by
        by_cases hsame : field.responseName = responseName
        · exact False.elim (hfield hsame)
        · simp [hsame]
      have hrest : responseName ∉ responseNames rest := by
        intro hmem
        apply hnotMem
        simp [responseNames]
        right
        simpa [responseNames] using hmem
      let responseNameDiffers : Semantic.Selection -> Bool := fun selection =>
        match selection.responseName? with
        | some name => !name == responseName
        | none => true
      have hhead : responseNameDiffers (toSelection field) = true := by
        simp [responseNameDiffers, toSelection, Semantic.Selection.responseName?,
          hfieldBool]
      have htail :
          List.filter responseNameDiffers (List.map toSelection rest)
            = List.map toSelection rest := by
        simpa [toSelectionSet, Semantic.SelectionSet.withoutFieldsWithResponseName,
          responseNameDiffers] using ih hrest
      rw [toSelectionSet, Semantic.SelectionSet.withoutFieldsWithResponseName]
      simp only [List.map_cons]
      change List.filter responseNameDiffers (toSelection field :: List.map toSelection rest)
        = toSelection field :: List.map toSelection rest
      rw [List.filter_cons_of_pos hhead, htail]

theorem normalizeSelectionSet_empty (schema : Schema)
    (fuel : Nat) (parentType : Name) :
    NormalForm.mergeFieldSelections.normalizeSelectionSet schema fuel parentType [] = [] := by
  cases fuel <;> simp [NormalForm.mergeFieldSelections.normalizeSelectionSet]

theorem normalizeSelectionSet_toSelectionSet (schema : Schema) :
    ∀ (fuel : Nat) (parentType : Name) (fields : List LeafField),
      fields.length <= fuel ->
        responseNamesNodup fields ->
          NormalForm.normalizeSelectionSet schema fuel parentType
            (toSelectionSet fields) = toSelectionSet fields := by
  intro fuel parentType fields
  induction fields generalizing fuel parentType with
  | nil =>
      intro _hfuel _hnodup
      simpa [toSelectionSet, NormalForm.normalizeSelectionSet]
        using normalizeSelectionSet_empty schema fuel parentType
  | cons field rest ih =>
      intro hfuel hnodup
      cases fuel with
      | zero =>
          simp at hfuel
      | succ fuel =>
          have hrestFuel : rest.length <= fuel := Nat.le_of_succ_le_succ hfuel
          have hnodupCons := hnodup
          simp [responseNamesNodup, responseNames] at hnodupCons
          rcases hnodupCons with ⟨hnotMem, hrestNodupRaw⟩
          have hnotMemNames : field.responseName ∉ responseNames rest := by
            intro hmem
            rcases (by simpa [responseNames] using hmem :
                ∃ x, x ∈ rest ∧ x.responseName = field.responseName) with
              ⟨existing, hexistingMem, hexistingName⟩
            exact hnotMem existing hexistingMem hexistingName
          have hrestNodup : responseNamesNodup rest := by
            simpa [responseNamesNodup, responseNames] using hrestNodupRaw
          have hfieldsWith :
              Semantic.SelectionSet.fieldsWithResponseName field.responseName
                (toSelection field :: List.map toSelection rest)
                  = [toSelection field] := by
            simpa [toSelectionSet]
              using fieldsWithResponseName_toSelectionSet_cons_self field rest
                hnotMemNames
          have hfieldsWith' :
              Semantic.SelectionSet.fieldsWithResponseName field.responseName
                (Semantic.Selection.field field.responseName field.fieldName
                  field.arguments [] [] :: List.map toSelection rest)
                  = [Semantic.Selection.field field.responseName field.fieldName
                    field.arguments [] []] := by
            simpa [toSelection] using hfieldsWith
          have hwithout :
              Semantic.SelectionSet.withoutFieldsWithResponseName field.responseName
                (List.map toSelection rest)
                  = List.map toSelection rest := by
            simpa [toSelectionSet]
              using withoutFieldsWithResponseName_toSelectionSet_notMem
                field.responseName rest hnotMemNames
          have hrestNorm :
              NormalForm.normalizeSelectionSet schema fuel parentType
                (List.map toSelection rest)
                  = List.map toSelection rest := by
            simpa [toSelectionSet] using ih fuel parentType hrestFuel hrestNodup
          have hrestNorm' :
              NormalForm.mergeFieldSelections.normalizeSelectionSet schema fuel
                parentType (List.map toSelection rest) = List.map toSelection rest := by
            simpa [NormalForm.normalizeSelectionSet] using hrestNorm
          cases hfieldReturn : schema.fieldReturnType? parentType field.fieldName <;>
            simp [NormalForm.normalizeSelectionSet,
              NormalForm.mergeFieldSelections.normalizeSelectionSet,
              NormalForm.mergeFieldSelections, toSelectionSet, toSelection,
              Semantic.Selection.responseName?, Semantic.Selection.subselections,
              Semantic.SelectionSet.mergeSelectionSets, hfieldsWith', hwithout,
              hrestNorm', hfieldReturn, normalizeSelectionSet_empty]

theorem normalizeSemanticOperation_toSelectionSet (schema : Schema)
    (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition) (fields : List LeafField) :
    responseNamesNodup fields ->
      NormalForm.normalizeSemanticOperation schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := toSelectionSet fields }
        = { name := name,
            rootType := rootType,
            variableDefinitions := variableDefinitions,
            selectionSet := toSelectionSet fields } := by
  intro hnodup
  simp [NormalForm.normalizeSemanticOperation, Semantic.Operation.size,
    toSelectionSet_size,
    normalizeSelectionSet_toSelectionSet schema fields.length rootType fields
      (Nat.le_refl fields.length) hnodup]

theorem selectionSetGroundTyped_toSelectionSet
    (schema : Schema) (fields : List LeafField) :
    NormalForm.selectionSetGroundTyped schema (toSelectionSet fields) := by
  unfold NormalForm.selectionSetGroundTyped
  constructor
  · exact Or.inl (selectionsAllFields_toSelectionSet fields)
  · intro selection hselection
    simp [toSelectionSet] at hselection
    rcases hselection with ⟨field, _hfield, rfl⟩
    simp [toSelection, NormalForm.selectionGroundTyped,
      NormalForm.selectionSetGroundTyped, NormalForm.selectionsAllFields]

theorem inlineFragmentTypeConditionsNodup_toSelectionSet
    (fields : List LeafField) :
    NormalForm.inlineFragmentTypeConditionsNodup (toSelectionSet fields) := by
  induction fields with
  | nil =>
      simp [toSelectionSet, NormalForm.inlineFragmentTypeConditionsNodup]
  | cons field rest ih =>
      have ih' :
          (List.filterMap
            ((fun selection =>
              match selection with
              | .inlineFragment (some typeCondition) _directives _selectionSet =>
                  some typeCondition
              | _ => none) ∘ toSelection) rest).Nodup := by
        simpa [toSelectionSet, NormalForm.inlineFragmentTypeConditionsNodup] using ih
      simpa [toSelectionSet, toSelection,
        NormalForm.inlineFragmentTypeConditionsNodup] using ih'

theorem selectionNonRedundant_toSelection (field : LeafField) :
    NormalForm.selectionNonRedundant field.toSelection := by
  simp [toSelection, NormalForm.selectionNonRedundant,
    NormalForm.selectionSetNonRedundant, NormalForm.responseNamesNodup,
    NormalForm.inlineFragmentTypeConditionsNodup]

theorem selectionSetNonRedundant_toSelectionSet (fields : List LeafField) :
    responseNamesNodup fields ->
      NormalForm.selectionSetNonRedundant (toSelectionSet fields) := by
  intro hnodup
  unfold NormalForm.selectionSetNonRedundant
  constructor
  · exact (normalForm_responseNamesNodup fields).2 hnodup
  · constructor
    · exact inlineFragmentTypeConditionsNodup_toSelectionSet fields
    · intro selection hselection
      simp [toSelectionSet] at hselection
      rcases hselection with ⟨field, _hfield, rfl⟩
      exact selectionNonRedundant_toSelection field

theorem selectionSetNormal_toSelectionSet
    (schema : Schema) (fields : List LeafField) :
    responseNamesNodup fields ->
      NormalForm.selectionSetNormal schema (toSelectionSet fields) := by
  intro hnodup
  exact And.intro (selectionSetGroundTyped_toSelectionSet schema fields)
    (selectionSetNonRedundant_toSelectionSet fields hnodup)

theorem semanticOperationNormal_toSelectionSet
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition) (fields : List LeafField) :
    responseNamesNodup fields ->
      NormalForm.semanticOperationNormal schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := toSelectionSet fields } := by
  intro hnodup
  exact selectionSetNormal_toSelectionSet schema fields hnodup

end LeafField

theorem typedResponseConformsToShapeBool_completeValue_emptySelection_emptyWithFuel
    (schema : Schema) (store : Store) (variableValues : Execution.VariableValues)
    (shapeFuel executionFuel : Nat) (parentType : Name) (value : Value) :
    typedResponseConformsToShapeBool variableValues shapeFuel
      (TypedExecution.completeValue schema store variableValues executionFuel parentType []
        value)
      ResponseShape.Shape.empty = true := by
  induction shapeFuel generalizing executionFuel parentType value with
  | zero =>
      simp [typedResponseConformsToShapeBool]
  | succ shapeFuel ih =>
      cases executionFuel with
      | zero =>
          cases value with
          | null =>
              simp [TypedExecution.completeValue, shallowTypedResponse,
                typedResponseConformsToShapeBool]
          | scalar scalarValue =>
              simp [TypedExecution.completeValue, shallowTypedResponse,
                typedResponseConformsToShapeBool, shapeEmptyBool, ResponseShape.Shape.empty]
          | object runtimeType id =>
              simp [TypedExecution.completeValue, shallowTypedResponse,
                typedResponseConformsToShapeBool,
                typedFieldsConformToShapeBool_nil]
          | list values =>
              induction values with
              | nil =>
                  simp [TypedExecution.completeValue, shallowTypedResponse,
                    shallowTypedResponses, typedResponseConformsToShapeBool]
              | cons value rest ihValues =>
                  have hvalue := ih 0 parentType value
                  have hvalue' :
                      typedResponseConformsToShapeBool variableValues shapeFuel
                        (shallowTypedResponse value) ResponseShape.Shape.empty = true := by
                    simpa [TypedExecution.completeValue] using hvalue
                  have hrest :
                      ∀ x, x ∈ shallowTypedResponses rest ->
                        typedResponseConformsToShapeBool variableValues shapeFuel x
                          ResponseShape.Shape.empty = true := by
                    simpa [TypedExecution.completeValue, shallowTypedResponse,
                      shallowTypedResponses, typedResponseConformsToShapeBool]
                      using ihValues
                  simp [TypedExecution.completeValue, shallowTypedResponse,
                    shallowTypedResponses, typedResponseConformsToShapeBool,
                    hvalue']
                  exact hrest
      | succ executionFuel =>
          cases value with
          | null =>
              simp [TypedExecution.completeValue, typedResponseConformsToShapeBool]
          | scalar scalarValue =>
              simp [TypedExecution.completeValue, typedResponseConformsToShapeBool,
                shapeEmptyBool, ResponseShape.Shape.empty]
          | object runtimeType id =>
              have hcollect :
                  Execution.collectFields schema variableValues executionFuel runtimeType
                    (Execution.Value.object runtimeType id) [] = [] := by
                cases executionFuel <;> rfl
              simpa [TypedExecution.completeValue, TypedExecution.executeSelectionSet,
                hcollect, TypedExecution.executeCollectedFields,
                typedResponseConformsToShapeBool]
                using typedFieldsConformToShapeBool_nil variableValues shapeFuel
                  runtimeType ResponseShape.Shape.empty
          | list values =>
              induction values with
              | nil =>
                  simp [TypedExecution.completeValue, typedResponseConformsToShapeBool]
              | cons value rest ihValues =>
                  have hvalue := ih executionFuel parentType value
                  have hrest :
                      ∀ x, x ∈ rest ->
                        typedResponseConformsToShapeBool variableValues shapeFuel
                          (TypedExecution.completeValue schema store variableValues
                            executionFuel parentType [] x)
                          ResponseShape.Shape.empty = true := by
                    simpa [TypedExecution.completeValue, typedResponseConformsToShapeBool]
                      using ihValues
                  simp [TypedExecution.completeValue, typedResponseConformsToShapeBool,
                    hvalue]
                  exact hrest

theorem typedResponseConformsToShapeBool_completeValue_emptySelection_empty
    (schema : Schema) (store : Store) (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name) (value : Value) :
    typedResponseConformsToShapeBool variableValues 1
      (TypedExecution.completeValue schema store variableValues fuel parentType [] value)
      ResponseShape.Shape.empty = true := by
  exact typedResponseConformsToShapeBool_completeValue_emptySelection_emptyWithFuel
    schema store variableValues 1 fuel parentType value

theorem groundNormalFormCorrect_twoDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (leftResponseName leftFieldName : Name) (leftArguments : List Argument)
    (rightResponseName rightFieldName : Name) (rightArguments : List Argument) :
    leftResponseName ≠ rightResponseName ->
      groundNormalFormCorrect schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [
            .field leftResponseName leftFieldName leftArguments [] [],
            .field rightResponseName rightFieldName rightArguments [] []
          ] } := by
  intro hdistinct
  rw [groundNormalFormCorrect]
  rw [NormalForm.normalizeSemanticOperation_twoDistinctLeafNoDirectives
    schema name rootType variableDefinitions leftResponseName leftFieldName leftArguments
    rightResponseName rightFieldName rightArguments hdistinct]
  exact semanticOperationsEquivalentOnDataWithFuel_refl schema _ _

theorem groundNormalFormCorrect_threeDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (firstResponseName firstFieldName : Name) (firstArguments : List Argument)
    (secondResponseName secondFieldName : Name) (secondArguments : List Argument)
    (thirdResponseName thirdFieldName : Name) (thirdArguments : List Argument) :
    firstResponseName ≠ secondResponseName ->
      firstResponseName ≠ thirdResponseName ->
      secondResponseName ≠ thirdResponseName ->
        groundNormalFormCorrect schema
          { name := name,
            rootType := rootType,
            variableDefinitions := variableDefinitions,
            selectionSet := [
              .field firstResponseName firstFieldName firstArguments [] [],
              .field secondResponseName secondFieldName secondArguments [] [],
              .field thirdResponseName thirdFieldName thirdArguments [] []
            ] } := by
  intro hfirstSecond hfirstThird hsecondThird
  rw [groundNormalFormCorrect]
  rw [NormalForm.normalizeSemanticOperation_threeDistinctLeafNoDirectives
    schema name rootType variableDefinitions firstResponseName firstFieldName firstArguments
    secondResponseName secondFieldName secondArguments thirdResponseName thirdFieldName
    thirdArguments hfirstSecond hfirstThird hsecondThird]
  exact semanticOperationsEquivalentOnDataWithFuel_refl schema _ _

theorem groundNormalFormCorrect_distinctLeafFieldsNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition) (fields : List LeafField) :
    LeafField.responseNamesNodup fields ->
      groundNormalFormCorrect schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := LeafField.toSelectionSet fields } := by
  intro hnodup
  rw [groundNormalFormCorrect]
  rw [LeafField.normalizeSemanticOperation_toSelectionSet schema name rootType
    variableDefinitions fields hnodup]
  exact semanticOperationsEquivalentOnDataWithFuel_refl schema _ _

set_option linter.unusedSimpArgs false in
theorem normalFormPreservesResponseShapeBool_twoDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (leftResponseName leftFieldName : Name) (leftArguments : List Argument)
    (rightResponseName rightFieldName : Name) (rightArguments : List Argument) :
    leftResponseName ≠ rightResponseName ->
      normalFormPreservesResponseShapeBool schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [
            .field leftResponseName leftFieldName leftArguments [] [],
            .field rightResponseName rightFieldName rightArguments [] []
          ] } = true := by
  intro hdistinct
  have hdistinct' : rightResponseName ≠ leftResponseName := Ne.symm hdistinct
  rw [normalFormPreservesResponseShapeBool]
  rw [NormalForm.normalizeSemanticOperation_twoDistinctLeafNoDirectives
    schema name rootType variableDefinitions leftResponseName leftFieldName leftArguments
    rightResponseName rightFieldName rightArguments hdistinct]
  by_cases hempty : schema.getPossibleTypes rootType = []
  · simp [ResponseShape.Shape.ofSemanticOperation,
      ResponseShape.Shape.semanticOperationShapeFuel,
      Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
      ResponseShape.Shape.semanticSelectionSetShape,
      ResponseShape.Shape.collectSelectionSetShapeFields,
      ResponseShape.Shape.collectSelectionShapeFields,
      ResponseShape.Condition.fromDirectives?, ResponseShape.Condition.empty,
      ResponseShape.Shape.empty, ResponseShape.Condition.satisfiableBool,
      ResponseShape.Condition.hasContradictionBool,
      ResponseShape.BooleanLiteral.hasContradictionBool,
      ResponseShape.Condition.possibleTypesEmptyBool,
      ResponseShape.Condition.and, ResponseShape.Shape.semanticOperationInitialCondition,
      hempty, ResponseShape.Shape.equivalentBool, ResponseShape.Shape.includesBool,
      ResponseShape.Shape.includesFieldsBool]
  · simp [ResponseShape.Shape.ofSemanticOperation,
      ResponseShape.Shape.semanticOperationShapeFuel,
      Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
      ResponseShape.Shape.semanticSelectionSetShape,
      ResponseShape.Shape.collectSelectionSetShapeFields,
      ResponseShape.Shape.collectSelectionShapeFields,
      ResponseShape.Condition.fromDirectives?, ResponseShape.Condition.empty,
      ResponseShape.Shape.empty, ResponseShape.Condition.satisfiableBool,
      ResponseShape.Condition.hasContradictionBool,
      ResponseShape.BooleanLiteral.hasContradictionBool,
      ResponseShape.Condition.possibleTypesEmptyBool,
      ResponseShape.Condition.and, ResponseShape.Shape.semanticOperationInitialCondition,
      hempty, hdistinct, hdistinct', ResponseShape.Shape.mergeFields,
      ResponseShape.Shape.merge, ResponseShape.Shape.size,
      ResponseShape.Shape.fieldsSize, ResponseShape.Shape.variantsSize,
      ResponseShape.Shape.mergeWithFuel, ResponseShape.Shape.mergeFieldsWithFuel,
      ResponseShape.Shape.equivalentBool, ResponseShape.Shape.includesBool,
      ResponseShape.Shape.includesFieldsBool, ResponseShape.Shape.includesVariantsBool,
      ResponseShape.Shape.lookupField, ResponseShape.Shape.lookupIncludingVariant,
      ResponseShape.VariantHeader.includedByBool_self,
      ResponseShape.Shape.empty_includesBool]

theorem normalFormPreservesResponseShape_twoDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (leftResponseName leftFieldName : Name) (leftArguments : List Argument)
    (rightResponseName rightFieldName : Name) (rightArguments : List Argument) :
    leftResponseName ≠ rightResponseName ->
      normalFormPreservesResponseShape schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [
            .field leftResponseName leftFieldName leftArguments [] [],
            .field rightResponseName rightFieldName rightArguments [] []
          ] } := by
  intro hdistinct
  exact normalFormPreservesResponseShapeBool_sound schema _
    (normalFormPreservesResponseShapeBool_twoDistinctLeafNoDirectives schema name rootType
      variableDefinitions leftResponseName leftFieldName leftArguments rightResponseName
      rightFieldName rightArguments hdistinct)

set_option linter.unusedSimpArgs false in
theorem normalFormPreservesResponseShapeBool_threeDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (firstResponseName firstFieldName : Name) (firstArguments : List Argument)
    (secondResponseName secondFieldName : Name) (secondArguments : List Argument)
    (thirdResponseName thirdFieldName : Name) (thirdArguments : List Argument) :
    firstResponseName ≠ secondResponseName ->
      firstResponseName ≠ thirdResponseName ->
      secondResponseName ≠ thirdResponseName ->
        normalFormPreservesResponseShapeBool schema
          { name := name,
            rootType := rootType,
            variableDefinitions := variableDefinitions,
            selectionSet := [
              .field firstResponseName firstFieldName firstArguments [] [],
              .field secondResponseName secondFieldName secondArguments [] [],
              .field thirdResponseName thirdFieldName thirdArguments [] []
            ] } = true := by
  intro hfirstSecond hfirstThird hsecondThird
  have hsecondFirst : secondResponseName ≠ firstResponseName := Ne.symm hfirstSecond
  have hthirdFirst : thirdResponseName ≠ firstResponseName := Ne.symm hfirstThird
  have hthirdSecond : thirdResponseName ≠ secondResponseName := Ne.symm hsecondThird
  rw [normalFormPreservesResponseShapeBool]
  rw [NormalForm.normalizeSemanticOperation_threeDistinctLeafNoDirectives
    schema name rootType variableDefinitions firstResponseName firstFieldName firstArguments
    secondResponseName secondFieldName secondArguments thirdResponseName thirdFieldName
    thirdArguments hfirstSecond hfirstThird hsecondThird]
  by_cases hempty : schema.getPossibleTypes rootType = []
  · simp [ResponseShape.Shape.ofSemanticOperation,
      ResponseShape.Shape.semanticOperationShapeFuel,
      Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
      ResponseShape.Shape.semanticSelectionSetShape,
      ResponseShape.Shape.collectSelectionSetShapeFields,
      ResponseShape.Shape.collectSelectionShapeFields,
      ResponseShape.Condition.fromDirectives?, ResponseShape.Condition.empty,
      ResponseShape.Shape.empty, ResponseShape.Condition.satisfiableBool,
      ResponseShape.Condition.hasContradictionBool,
      ResponseShape.BooleanLiteral.hasContradictionBool,
      ResponseShape.Condition.possibleTypesEmptyBool,
      ResponseShape.Condition.and, ResponseShape.Shape.semanticOperationInitialCondition,
      hempty, ResponseShape.Shape.equivalentBool, ResponseShape.Shape.includesBool,
      ResponseShape.Shape.includesFieldsBool]
  · simp [ResponseShape.Shape.ofSemanticOperation,
      ResponseShape.Shape.semanticOperationShapeFuel,
      Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
      ResponseShape.Shape.semanticSelectionSetShape,
      ResponseShape.Shape.collectSelectionSetShapeFields,
      ResponseShape.Shape.collectSelectionShapeFields,
      ResponseShape.Condition.fromDirectives?, ResponseShape.Condition.empty,
      ResponseShape.Shape.empty, ResponseShape.Condition.satisfiableBool,
      ResponseShape.Condition.hasContradictionBool,
      ResponseShape.BooleanLiteral.hasContradictionBool,
      ResponseShape.Condition.possibleTypesEmptyBool,
      ResponseShape.Condition.and, ResponseShape.Shape.semanticOperationInitialCondition,
      hempty, hfirstSecond, hfirstThird, hsecondThird, hsecondFirst, hthirdFirst,
      hthirdSecond, ResponseShape.Shape.mergeFields, ResponseShape.Shape.merge,
      ResponseShape.Shape.size, ResponseShape.Shape.fieldsSize,
      ResponseShape.Shape.variantsSize, ResponseShape.Shape.mergeWithFuel,
      ResponseShape.Shape.mergeFieldsWithFuel, ResponseShape.Shape.equivalentBool,
      ResponseShape.Shape.includesBool, ResponseShape.Shape.includesFieldsBool,
      ResponseShape.Shape.includesVariantsBool, ResponseShape.Shape.lookupField,
      ResponseShape.Shape.lookupIncludingVariant,
      ResponseShape.VariantHeader.includedByBool_self,
      ResponseShape.Shape.empty_includesBool]

theorem normalFormPreservesResponseShape_threeDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (firstResponseName firstFieldName : Name) (firstArguments : List Argument)
    (secondResponseName secondFieldName : Name) (secondArguments : List Argument)
    (thirdResponseName thirdFieldName : Name) (thirdArguments : List Argument) :
    firstResponseName ≠ secondResponseName ->
      firstResponseName ≠ thirdResponseName ->
      secondResponseName ≠ thirdResponseName ->
        normalFormPreservesResponseShape schema
          { name := name,
            rootType := rootType,
            variableDefinitions := variableDefinitions,
            selectionSet := [
              .field firstResponseName firstFieldName firstArguments [] [],
              .field secondResponseName secondFieldName secondArguments [] [],
              .field thirdResponseName thirdFieldName thirdArguments [] []
            ] } := by
  intro hfirstSecond hfirstThird hsecondThird
  exact normalFormPreservesResponseShapeBool_sound schema _
    (normalFormPreservesResponseShapeBool_threeDistinctLeafNoDirectives schema name rootType
      variableDefinitions firstResponseName firstFieldName firstArguments secondResponseName
      secondFieldName secondArguments thirdResponseName thirdFieldName thirdArguments
      hfirstSecond hfirstThird hsecondThird)

set_option linter.unusedSimpArgs false in
theorem responseShapeCorrectForTypedExecutionAtRoot_twoDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (leftResponseName leftFieldName : Name) (leftArguments : List Argument)
    (rightResponseName rightFieldName : Name) (rightArguments : List Argument) :
    leftResponseName ≠ rightResponseName ->
      responseShapeCorrectForTypedExecutionAtRoot schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [
            .field leftResponseName leftFieldName leftArguments [] [],
            .field rightResponseName rightFieldName rightArguments [] []
          ] } := by
  intro hdistinct store variableValues root _hstore _hroot hrootType
  have hrootType' : schema.typeIncludesObject rootType root.typeName := hrootType
  have hnonempty : ¬ schema.getPossibleTypes rootType = [] :=
    possibleTypes_nonempty_of_typeIncludesObject schema hrootType'
  simp [TypedExecution.executeSemanticQuery, Execution.executeSemanticQueryFuel,
    Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
    TypedExecution.executeSelectionSet, Execution.collectFields, Execution.collectSelection,
    Execution.selectionDirectivesAllowBool, Execution.mergeExecutableGroups,
    Execution.addExecutableGroup, Execution.addExecutableFields,
    Execution.addExecutableField, hdistinct, TypedExecution.executeCollectedFields,
    TypedExecution.executeField, Execution.mergedFieldSelectionSet,
    ResponseShape.Shape.ofSemanticOperation,
    ResponseShape.Shape.semanticOperationShapeFuel,
    ResponseShape.Shape.semanticSelectionSetShape,
    ResponseShape.Shape.collectSelectionSetShapeFields,
    ResponseShape.Shape.collectSelectionShapeFields,
    ResponseShape.Condition.fromDirectives?, ResponseShape.Condition.empty,
    ResponseShape.Shape.empty, ResponseShape.Condition.satisfiableBool,
    ResponseShape.Condition.hasContradictionBool,
    ResponseShape.BooleanLiteral.hasContradictionBool,
    ResponseShape.Condition.possibleTypesEmptyBool,
    ResponseShape.Condition.and, ResponseShape.Shape.semanticOperationInitialCondition,
    hnonempty, ResponseShape.Shape.mergeFields, ResponseShape.Shape.merge,
    ResponseShape.Shape.size, ResponseShape.Shape.fieldsSize,
    ResponseShape.Shape.variantsSize, ResponseShape.Shape.mergeWithFuel,
    ResponseShape.Shape.mergeFieldsWithFuel, typedResponseConformsToShapeBool,
    typedFieldsConformToShapeBool, typedVariantConformsToShapeBool,
    variantHeaderActiveBool, conditionHoldsBool,
    possibleTypesHoldBool_of_typeIncludesObject schema hrootType',
    TypedExecution.completeValue, TypedExecution.executeSelectionSet,
    Execution.collectFields,
    typedResponseConformsToShapeBool_completeValue_emptySelection_empty,
    ResponseShape.Shape.lookupField]

set_option linter.unusedSimpArgs false in
theorem responseShapeCorrectForTypedExecutionAtRoot_threeDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (firstResponseName firstFieldName : Name) (firstArguments : List Argument)
    (secondResponseName secondFieldName : Name) (secondArguments : List Argument)
    (thirdResponseName thirdFieldName : Name) (thirdArguments : List Argument) :
    firstResponseName ≠ secondResponseName ->
      firstResponseName ≠ thirdResponseName ->
      secondResponseName ≠ thirdResponseName ->
        responseShapeCorrectForTypedExecutionAtRoot schema
          { name := name,
            rootType := rootType,
            variableDefinitions := variableDefinitions,
            selectionSet := [
              .field firstResponseName firstFieldName firstArguments [] [],
              .field secondResponseName secondFieldName secondArguments [] [],
              .field thirdResponseName thirdFieldName thirdArguments [] []
            ] } := by
  intro hfirstSecond hfirstThird hsecondThird store variableValues root _hstore _hroot
    hrootType
  have hrootType' : schema.typeIncludesObject rootType root.typeName := hrootType
  have hnonempty : ¬ schema.getPossibleTypes rootType = [] :=
    possibleTypes_nonempty_of_typeIncludesObject schema hrootType'
  have hsecondFirst : secondResponseName ≠ firstResponseName := Ne.symm hfirstSecond
  have hthirdFirst : thirdResponseName ≠ firstResponseName := Ne.symm hfirstThird
  have hthirdSecond : thirdResponseName ≠ secondResponseName := Ne.symm hsecondThird
  have hfirstComplete :
      typedResponseConformsToShapeBool variableValues 1
        (TypedExecution.completeValue schema store variableValues 9
          ((schema.fieldReturnType? rootType firstFieldName).getD firstFieldName) []
          (store.resolveValue firstFieldName firstArguments
            (Value.object root.typeName root.id)))
        { fields := [] } = true := by
    simpa [ResponseShape.Shape.empty]
      using typedResponseConformsToShapeBool_completeValue_emptySelection_empty
        schema store variableValues 9
        ((schema.fieldReturnType? rootType firstFieldName).getD firstFieldName)
        (store.resolveValue firstFieldName firstArguments
          (Value.object root.typeName root.id))
  have hsecondComplete :
      typedResponseConformsToShapeBool variableValues 1
        (TypedExecution.completeValue schema store variableValues 9
          ((schema.fieldReturnType? rootType secondFieldName).getD secondFieldName) []
          (store.resolveValue secondFieldName secondArguments
            (Value.object root.typeName root.id)))
        { fields := [] } = true := by
    simpa [ResponseShape.Shape.empty]
      using typedResponseConformsToShapeBool_completeValue_emptySelection_empty
        schema store variableValues 9
        ((schema.fieldReturnType? rootType secondFieldName).getD secondFieldName)
        (store.resolveValue secondFieldName secondArguments
          (Value.object root.typeName root.id))
  have hthirdComplete :
      typedResponseConformsToShapeBool variableValues 1
        (TypedExecution.completeValue schema store variableValues 9
          ((schema.fieldReturnType? rootType thirdFieldName).getD thirdFieldName) []
          (store.resolveValue thirdFieldName thirdArguments
            (Value.object root.typeName root.id)))
        { fields := [] } = true := by
    simpa [ResponseShape.Shape.empty]
      using typedResponseConformsToShapeBool_completeValue_emptySelection_empty
        schema store variableValues 9
        ((schema.fieldReturnType? rootType thirdFieldName).getD thirdFieldName)
        (store.resolveValue thirdFieldName thirdArguments
          (Value.object root.typeName root.id))
  simp [TypedExecution.executeSemanticQuery, Execution.executeSemanticQueryFuel,
    Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
    TypedExecution.executeSelectionSet, Execution.collectFields, Execution.collectSelection,
    Execution.selectionDirectivesAllowBool, Execution.mergeExecutableGroups,
    Execution.addExecutableGroup, Execution.addExecutableFields,
    Execution.addExecutableField, hfirstSecond, hfirstThird, hsecondThird, hsecondFirst,
    hthirdFirst, hthirdSecond, TypedExecution.executeCollectedFields,
    TypedExecution.executeField, Execution.mergedFieldSelectionSet,
    ResponseShape.Shape.ofSemanticOperation,
    ResponseShape.Shape.semanticOperationShapeFuel,
    ResponseShape.Shape.semanticSelectionSetShape,
    ResponseShape.Shape.collectSelectionSetShapeFields,
    ResponseShape.Shape.collectSelectionShapeFields,
    ResponseShape.Condition.fromDirectives?, ResponseShape.Condition.empty,
    ResponseShape.Shape.empty, ResponseShape.Condition.satisfiableBool,
    ResponseShape.Condition.hasContradictionBool,
    ResponseShape.BooleanLiteral.hasContradictionBool,
    ResponseShape.Condition.possibleTypesEmptyBool,
    ResponseShape.Condition.and, ResponseShape.Shape.semanticOperationInitialCondition,
    hnonempty, ResponseShape.Shape.mergeFields, ResponseShape.Shape.merge,
    ResponseShape.Shape.size, ResponseShape.Shape.fieldsSize,
    ResponseShape.Shape.variantsSize, ResponseShape.Shape.mergeWithFuel,
    ResponseShape.Shape.mergeFieldsWithFuel, typedResponseConformsToShapeBool,
    typedFieldsConformToShapeBool, typedVariantConformsToShapeBool,
    variantHeaderActiveBool, conditionHoldsBool,
    possibleTypesHoldBool_of_typeIncludesObject schema hrootType',
    hfirstComplete, hsecondComplete, hthirdComplete,
    ResponseShape.Shape.lookupField]

end DataModel

end GraphQL
