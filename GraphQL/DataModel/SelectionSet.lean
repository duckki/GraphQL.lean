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

def toExecutableField (parentType : Name) (field : LeafField) :
    Execution.ExecutableField :=
  {
    parentType := parentType,
    responseName := field.responseName,
    fieldName := field.fieldName,
    arguments := field.arguments,
    selectionSet := []
  }

def toExecutableGroups (parentType : Name) (fields : List LeafField) :
    List (Name × List Execution.ExecutableField) :=
  fields.map (fun field => (field.responseName, [toExecutableField parentType field]))

def typedResponseField (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType : Name) (source : Value) (field : LeafField) :
    Name × TypedResponse :=
  (field.responseName,
    TypedExecution.completeValue schema store variableValues fuel
      ((schema.fieldReturnType? parentType field.fieldName).getD field.fieldName) []
      (store.resolveValue field.fieldName field.arguments source))

def typedResponseFields (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType : Name) (source : Value) (fields : List LeafField) :
    List (Name × TypedResponse) :=
  fields.map (typedResponseField schema store variableValues fuel parentType source)

def toShapeVariant (condition : ResponseShape.Condition) (field : LeafField) :
    ResponseShape.Shape.Variant :=
  ((condition, ResponseShape.selectedField field.fieldName field.arguments),
    ResponseShape.Shape.empty)

def toShapeField (condition : ResponseShape.Condition) (field : LeafField) :
    Name × List ResponseShape.Shape.Variant :=
  (field.responseName, [toShapeVariant condition field])

def toShapeFields (condition : ResponseShape.Condition)
    (fields : List LeafField) :
    List (Name × List ResponseShape.Shape.Variant) :=
  fields.map (toShapeField condition)

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

theorem collectSelection_toSelection (schema : Schema)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType : Name) (source : Execution.Value) (field : LeafField) :
    Execution.collectSelection schema variableValues (fuel + 1) parentType source
      field.toSelection = [(field.responseName, [toExecutableField parentType field])] := by
  cases field
  simp [toSelection, toExecutableField, Execution.collectSelection,
    Execution.selectionDirectivesAllowBool]

theorem executeCollectedFields_toExecutableGroups
    (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType : Name) (source : Value) (fields : List LeafField) :
    TypedExecution.executeCollectedFields schema store variableValues (fuel + 1) source
      (toExecutableGroups parentType fields)
      = typedResponseFields schema store variableValues fuel parentType source fields := by
  induction fields with
  | nil =>
      simp [toExecutableGroups, typedResponseFields,
        TypedExecution.executeCollectedFields]
  | cons field rest ih =>
      have ih' :
          TypedExecution.executeCollectedFields schema store variableValues (fuel + 1) source
            (List.map
              (fun field =>
                (field.responseName, [toExecutableField parentType field]))
              rest)
            = List.map
                (typedResponseField schema store variableValues fuel parentType source)
                rest := by
        simpa [toExecutableGroups, typedResponseFields] using ih
      have ih'' :
          TypedExecution.executeCollectedFields schema store variableValues (fuel + 1) source
            (List.map
              (fun field =>
                (field.responseName,
                  [{
                    parentType := parentType,
                    responseName := field.responseName,
                    fieldName := field.fieldName,
                    arguments := field.arguments,
                    selectionSet := []
                  }]))
              rest)
            = List.map
                (typedResponseField schema store variableValues fuel parentType source)
                rest := by
        simpa [toExecutableField] using ih'
      simp [toExecutableGroups, typedResponseFields, typedResponseField,
        toExecutableField, TypedExecution.executeCollectedFields,
        TypedExecution.executeField, Execution.mergedFieldSelectionSet, ih'']

theorem addExecutableField_toExecutableGroups_append
    (parentType : Name) (field : LeafField) (fields : List LeafField) :
    field.responseName ∉ responseNames fields ->
      Execution.addExecutableField (toExecutableField parentType field)
        (toExecutableGroups parentType fields)
        = toExecutableGroups parentType (fields ++ [field]) := by
  intro hnotMem
  induction fields with
  | nil =>
      simp [toExecutableGroups, toExecutableField, Execution.addExecutableField]
  | cons existing rest ih =>
      have hhead : existing.responseName ≠ field.responseName := by
        intro hsame
        apply hnotMem
        simp [responseNames, hsame]
      have hheadBool : (existing.responseName == field.responseName) = false := by
        by_cases hsame : existing.responseName = field.responseName
        · exact False.elim (hhead hsame)
        · simp [hsame]
      have hrest : field.responseName ∉ responseNames rest := by
        intro hmem
        apply hnotMem
        simp [responseNames]
        right
        simpa [responseNames] using hmem
      have ih' :
          Execution.addExecutableField
            {
              parentType := parentType,
              responseName := field.responseName,
              fieldName := field.fieldName,
              arguments := field.arguments,
              selectionSet := []
            }
            (List.map
              (fun field =>
                (field.responseName,
                  [{
                    parentType := parentType,
                    responseName := field.responseName,
                    fieldName := field.fieldName,
                    arguments := field.arguments,
                    selectionSet := []
                  }]))
              rest)
            =
              List.map
                (fun field =>
                  (field.responseName,
                    [{
                      parentType := parentType,
                      responseName := field.responseName,
                      fieldName := field.fieldName,
                      arguments := field.arguments,
                      selectionSet := []
                    }]))
                rest ++
              [(field.responseName,
                [{
                  parentType := parentType,
                  responseName := field.responseName,
                  fieldName := field.fieldName,
                  arguments := field.arguments,
                  selectionSet := []
                }])] := by
        simpa [toExecutableGroups, toExecutableField] using ih hrest
      simp [toExecutableGroups, toExecutableField, Execution.addExecutableField,
        hheadBool, ih']

theorem addExecutableGroup_toExecutableGroups_append
    (parentType : Name) (field : LeafField) (fields : List LeafField) :
    field.responseName ∉ responseNames fields ->
      Execution.addExecutableGroup
        (field.responseName, [toExecutableField parentType field])
        (toExecutableGroups parentType fields)
        = toExecutableGroups parentType (fields ++ [field]) := by
  intro hnotMem
  simp [Execution.addExecutableGroup, Execution.addExecutableFields,
    addExecutableField_toExecutableGroups_append parentType field fields hnotMem]

theorem mergeExecutableGroups_toExecutableGroups_append
    (parentType : Name) (leftFields suffix : List LeafField) :
    responseNamesNodup (leftFields ++ suffix) ->
      Execution.mergeExecutableGroups
        (toExecutableGroups parentType leftFields)
        (toExecutableGroups parentType suffix)
        = toExecutableGroups parentType (leftFields ++ suffix) := by
  induction suffix generalizing leftFields with
  | nil =>
      intro _hnodup
      simp [toExecutableGroups, Execution.mergeExecutableGroups]
  | cons field rest ih =>
      intro hnodup
      have hnameParts :
          (responseNames leftFields ++ field.responseName :: responseNames rest).Nodup := by
        simpa [responseNamesNodup, responseNames, List.map_append] using hnodup
      simp [List.nodup_append] at hnameParts
      rcases hnameParts with ⟨_hprefix, _hfieldRest, hseparate⟩
      have hnotMemPrefix : field.responseName ∉ responseNames leftFields := by
        intro hmem
        exact (hseparate field.responseName hmem).left rfl
      have hrestNodup : responseNamesNodup ((leftFields ++ [field]) ++ rest) := by
        simpa [responseNamesNodup, responseNames, List.map_append,
          List.append_assoc] using hnodup
      have hhead :=
        addExecutableGroup_toExecutableGroups_append parentType field leftFields
          hnotMemPrefix
      have htail := ih (leftFields ++ [field]) hrestNodup
      rw [toExecutableGroups, Execution.mergeExecutableGroups]
      change Execution.mergeExecutableGroups
        (Execution.addExecutableGroup
          (field.responseName, [toExecutableField parentType field])
          (toExecutableGroups parentType leftFields))
        (toExecutableGroups parentType rest)
          = toExecutableGroups parentType (leftFields ++ field :: rest)
      rw [hhead, htail]
      simp [toExecutableGroups, List.append_assoc]

theorem collectFields_toSelectionSet (schema : Schema)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType : Name) (source : Execution.Value) (fields : List LeafField) :
    responseNamesNodup fields ->
      Execution.collectFields schema variableValues (fuel + 1) parentType source
        (toSelectionSet fields)
        = toExecutableGroups parentType fields := by
  intro hnodup
  induction fields with
  | nil =>
      simp [toSelectionSet, toExecutableGroups, Execution.collectFields]
  | cons field rest ih =>
      have hnodupCons := hnodup
      simp [responseNamesNodup, responseNames] at hnodupCons
      rcases hnodupCons with ⟨_hnotMem, hrestNodupRaw⟩
      have hrestNodup : responseNamesNodup rest := by
        simpa [responseNamesNodup, responseNames] using hrestNodupRaw
      have hcollectSelection :=
        collectSelection_toSelection schema variableValues fuel parentType source field
      have hcollectRest :=
        ih hrestNodup
      have hcollectRest' :
          Execution.collectFields schema variableValues (fuel + 1) parentType source
            (List.map toSelection rest)
            = toExecutableGroups parentType rest := by
        simpa [toSelectionSet] using hcollectRest
      have hmerge :
          Execution.mergeExecutableGroups
            (toExecutableGroups parentType [field])
            (toExecutableGroups parentType rest)
            = toExecutableGroups parentType ([field] ++ rest) :=
        mergeExecutableGroups_toExecutableGroups_append parentType [field] rest
          (by simpa [responseNamesNodup] using hnodup)
      have hmerge' :
          Execution.mergeExecutableGroups
            [(field.responseName, [toExecutableField parentType field])]
            (toExecutableGroups parentType rest)
            =
              (field.responseName, [toExecutableField parentType field]) ::
                List.map
                  (fun field =>
                    (field.responseName, [toExecutableField parentType field]))
                  rest := by
        simpa [toExecutableGroups] using hmerge
      have hmerge'' :
          Execution.mergeExecutableGroups
            [(field.responseName, [toExecutableField parentType field])]
            (List.map
              (fun field =>
                (field.responseName, [toExecutableField parentType field]))
              rest)
            =
              (field.responseName, [toExecutableField parentType field]) ::
                List.map
                  (fun field =>
                    (field.responseName, [toExecutableField parentType field]))
                  rest := by
        simpa [toExecutableGroups] using hmerge'
      simp [toSelectionSet, toExecutableGroups, Execution.collectFields,
        hcollectSelection, hcollectRest', hmerge'']

theorem executeSelectionSet_toSelectionSet
    (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType : Name) (source : Value) (fields : List LeafField) :
    responseNamesNodup fields ->
      TypedExecution.executeSelectionSet schema store variableValues (fuel + 1)
        parentType source (toSelectionSet fields)
        = typedResponseFields schema store variableValues fuel parentType source fields := by
  intro hnodup
  simp [TypedExecution.executeSelectionSet,
    collectFields_toSelectionSet schema variableValues fuel parentType
      source.toExecutionValue fields hnodup,
    executeCollectedFields_toExecutableGroups]

theorem executeSemanticQuery_toSelectionSet
    (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues)
    (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition) (fields : List LeafField)
    (root : Root) :
    responseNamesNodup fields ->
      TypedExecution.executeSemanticQuery schema store variableValues
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := toSelectionSet fields }
        root
        = .object root.typeName
          (typedResponseFields schema store variableValues (fields.length * 3)
            rootType (.object root.typeName root.id) fields) := by
  intro hnodup
  simp [TypedExecution.executeSemanticQuery, Execution.executeSemanticQueryFuel,
    Semantic.Operation.size, toSelectionSet_size,
    executeSelectionSet_toSelectionSet schema store variableValues (fields.length * 3)
      rootType (.object root.typeName root.id) fields hnodup]

theorem lookupField_toShapeFields_notMem
    (condition : ResponseShape.Condition) (responseName : Name)
    (fields : List LeafField) :
    responseName ∉ responseNames fields ->
      ResponseShape.Shape.lookupField responseName
        (toShapeFields condition fields) = none := by
  intro hnotMem
  induction fields with
  | nil =>
      simp [toShapeFields, ResponseShape.Shape.lookupField]
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
      have ih' :
          ResponseShape.Shape.lookupField responseName
            (List.map (toShapeField condition) rest) = none := by
        simpa [toShapeFields] using ih hrest
      simp [toShapeFields, toShapeField, ResponseShape.Shape.lookupField,
        hfieldBool, ih']

theorem lookupField_toShapeFields_cons_self
    (condition : ResponseShape.Condition) (field : LeafField)
    (rest : List LeafField) :
    ResponseShape.Shape.lookupField field.responseName
      (toShapeFields condition (field :: rest))
      = some [toShapeVariant condition field] := by
  simp [toShapeFields, toShapeField, ResponseShape.Shape.lookupField]

theorem lookupField_toShapeFields_append_cons_self
    (condition : ResponseShape.Condition) (shapePrefix : List LeafField)
    (field : LeafField) (rest : List LeafField) :
    field.responseName ∉ responseNames shapePrefix ->
      ResponseShape.Shape.lookupField field.responseName
        (toShapeFields condition (shapePrefix ++ field :: rest))
        = some [toShapeVariant condition field] := by
  intro hnotMem
  induction shapePrefix with
  | nil =>
      simp [toShapeFields, toShapeField, ResponseShape.Shape.lookupField]
  | cons existing shapePrefix ih =>
      have hhead : existing.responseName ≠ field.responseName := by
        intro hsame
        apply hnotMem
        simp [responseNames, hsame]
      have hheadBool : (existing.responseName == field.responseName) = false := by
        by_cases hsame : existing.responseName = field.responseName
        · exact False.elim (hhead hsame)
        · simp [hsame]
      have hprefix : field.responseName ∉ responseNames shapePrefix := by
        intro hmem
        apply hnotMem
        simp [responseNames]
        right
        simpa [responseNames] using hmem
      have ih' :
          ResponseShape.Shape.lookupField field.responseName
            (List.map (toShapeField condition) shapePrefix ++
              (field.responseName, [toShapeVariant condition field]) ::
                List.map (toShapeField condition) rest)
            = some [toShapeVariant condition field] := by
        simpa [toShapeFields] using ih hprefix
      simp [toShapeFields, toShapeField, ResponseShape.Shape.lookupField,
        hheadBool, ih']

theorem shapeFieldFilter_eq_nil_notMem
    (condition : ResponseShape.Condition) (responseName : Name)
    (fields : List LeafField) :
    responseName ∉ responseNames fields ->
      (toShapeFields condition fields).filter
        (fun field => field.fst == responseName) = [] := by
  intro hnotMem
  induction fields with
  | nil =>
      simp [toShapeFields]
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
      have hrestAll : ∀ a, a ∈ rest -> ¬a.responseName = responseName := by
        intro existing hexisting hsame
        apply hrest
        simp [responseNames]
        exact ⟨existing, hexisting, hsame⟩
      simpa [toShapeFields, toShapeField, hfieldBool] using hrestAll

theorem shapeFieldFilter_ne_eq_self_notMem
    (condition : ResponseShape.Condition) (responseName : Name)
    (fields : List LeafField) :
    responseName ∉ responseNames fields ->
      (toShapeFields condition fields).filter
        (fun field => !(field.fst == responseName)) = toShapeFields condition fields := by
  intro hnotMem
  induction fields with
  | nil =>
      simp [toShapeFields]
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
      have hrestAll : ∀ a, a ∈ rest -> ¬a.responseName = responseName := by
        intro existing hexisting hsame
        apply hrest
        simp [responseNames]
        exact ⟨existing, hexisting, hsame⟩
      simpa [toShapeFields, toShapeField, hfieldBool] using hrestAll

theorem mergeFieldsWithFuel_toShapeFields_append
    (condition : ResponseShape.Condition) :
    ∀ (fuel : Nat) (leftFields suffix : List LeafField),
      suffix.length <= fuel ->
        responseNamesNodup (leftFields ++ suffix) ->
          ResponseShape.Shape.mergeFieldsWithFuel fuel
            (toShapeFields condition leftFields)
            (toShapeFields condition suffix)
            = toShapeFields condition (leftFields ++ suffix) := by
  intro fuel leftFields suffix
  induction suffix generalizing fuel leftFields with
  | nil =>
      intro _hfuel _hnodup
      cases fuel <;> simp [toShapeFields, ResponseShape.Shape.mergeFieldsWithFuel]
  | cons field rest ih =>
      intro hfuel hnodup
      cases fuel with
      | zero =>
          simp at hfuel
      | succ fuel =>
          have hrestFuel : rest.length <= fuel := Nat.le_of_succ_le_succ hfuel
          have hnameParts :
              (responseNames leftFields ++ field.responseName :: responseNames rest).Nodup := by
            simpa [responseNamesNodup, responseNames, List.map_append] using hnodup
          simp [List.nodup_append] at hnameParts
          rcases hnameParts with ⟨_hleft, _hfieldRest, hseparate⟩
          have hnotMemLeft : field.responseName ∉ responseNames leftFields := by
            intro hmem
            exact (hseparate field.responseName hmem).left rfl
          have hmatching :
              (toShapeFields condition leftFields).filter
                (fun shapeField => shapeField.fst == field.responseName) = [] :=
            shapeFieldFilter_eq_nil_notMem condition field.responseName leftFields
              hnotMemLeft
          have hmatching' :
              List.filter (fun shapeField => shapeField.fst == field.responseName)
                (List.map (toShapeField condition) leftFields) = [] := by
            simpa [toShapeFields] using hmatching
          have hremaining :
              (toShapeFields condition leftFields).filter
                (fun shapeField => !(shapeField.fst == field.responseName))
                = toShapeFields condition leftFields :=
            shapeFieldFilter_ne_eq_self_notMem condition field.responseName leftFields
              hnotMemLeft
          have hremaining' :
              List.filter (fun shapeField => !(shapeField.fst == field.responseName))
                (List.map (toShapeField condition) leftFields)
                = List.map (toShapeField condition) leftFields := by
            simpa [toShapeFields] using hremaining
          have hrestNodup : responseNamesNodup ((leftFields ++ [field]) ++ rest) := by
            simpa [responseNamesNodup, responseNames, List.map_append,
              List.append_assoc] using hnodup
          have htail :
              ResponseShape.Shape.mergeFieldsWithFuel fuel
                (toShapeFields condition leftFields ++ [toShapeField condition field])
                (toShapeFields condition rest)
                = toShapeFields condition ((leftFields ++ [field]) ++ rest) := by
            simpa [toShapeFields, List.map_append] using
              ih fuel (leftFields ++ [field]) hrestFuel hrestNodup
          have htail' :
              ResponseShape.Shape.mergeFieldsWithFuel fuel
                (List.map (toShapeField condition) leftFields ++
                  [(field.responseName, [toShapeVariant condition field])])
                (List.map (toShapeField condition) rest)
                =
                  List.map (toShapeField condition) leftFields ++
                    (field.responseName, [toShapeVariant condition field]) ::
                      List.map (toShapeField condition) rest := by
            simpa [toShapeFields, toShapeField, List.map_append,
              List.append_assoc] using htail
          simp [toShapeFields, toShapeField, ResponseShape.Shape.mergeFieldsWithFuel,
            hmatching', hremaining', htail']

theorem shapeFieldsSize_toShapeFields
    (condition : ResponseShape.Condition) (fields : List LeafField) :
    ResponseShape.Shape.fieldsSize (toShapeFields condition fields)
      = fields.length := by
  induction fields with
  | nil =>
      simp [toShapeFields, ResponseShape.Shape.fieldsSize]
  | cons field rest ih =>
      have ih' :
          ResponseShape.Shape.fieldsSize (List.map (toShapeField condition) rest)
            = rest.length := by
        simpa [toShapeFields] using ih
      simp [toShapeFields, toShapeField, toShapeVariant,
        ResponseShape.Shape.fieldsSize, ResponseShape.Shape.variantsSize,
        ResponseShape.Shape.empty, ResponseShape.Shape.size, ih', Nat.add_comm]

theorem mergeFields_toShapeFields_append
    (condition : ResponseShape.Condition)
    (leftFields suffix : List LeafField) :
    responseNamesNodup (leftFields ++ suffix) ->
      ResponseShape.Shape.mergeFields
        (toShapeFields condition leftFields)
        (toShapeFields condition suffix)
        = toShapeFields condition (leftFields ++ suffix) := by
  intro hnodup
  have hfuel :
      suffix.length <=
        ResponseShape.Shape.fieldsSize (toShapeFields condition leftFields)
          + ResponseShape.Shape.size ⟨toShapeFields condition suffix⟩ := by
    simp [ResponseShape.Shape.size, shapeFieldsSize_toShapeFields]
    omega
  have hfuelEq :
      ResponseShape.Shape.size ⟨toShapeFields condition leftFields⟩
        + ResponseShape.Shape.size ⟨toShapeFields condition suffix⟩
        =
          (ResponseShape.Shape.fieldsSize (toShapeFields condition leftFields)
            + ResponseShape.Shape.size ⟨toShapeFields condition suffix⟩) + 1 := by
    simp [ResponseShape.Shape.size]
    omega
  rw [ResponseShape.Shape.mergeFields, ResponseShape.Shape.merge, hfuelEq]
  simp [ResponseShape.Shape.mergeWithFuel]
  exact mergeFieldsWithFuel_toShapeFields_append condition
      (ResponseShape.Shape.fieldsSize (toShapeFields condition leftFields)
        + ResponseShape.Shape.size ⟨toShapeFields condition suffix⟩)
      leftFields suffix hfuel hnodup

theorem mergeFields_parentVariant_twoChildShapeFields
    (parentResponseName : Name) (parentHeader : ResponseShape.VariantHeader)
    (childCondition : ResponseShape.Condition) (left right : LeafField) :
    left.responseName ≠ right.responseName ->
      ResponseShape.Shape.mergeFields
        [(parentResponseName,
          [(parentHeader, ⟨toShapeFields childCondition [left]⟩)])]
        [(parentResponseName,
          [(parentHeader, ⟨toShapeFields childCondition [right]⟩)])]
        =
          [(parentResponseName,
            [(parentHeader, ⟨toShapeFields childCondition [left, right]⟩)])] := by
  intro hdistinct
  cases left
  cases right
  simp [toShapeFields, toShapeField, toShapeVariant, ResponseShape.Shape.mergeFields,
    ResponseShape.Shape.merge, ResponseShape.Shape.size, ResponseShape.Shape.fieldsSize,
    ResponseShape.Shape.variantsSize, ResponseShape.Shape.mergeWithFuel,
    ResponseShape.Shape.mergeFieldsWithFuel, ResponseShape.Shape.mergeVariantsWithFuel,
    ResponseShape.VariantHeader.eqBool_self, ResponseShape.Shape.empty, hdistinct]

theorem collectSelectionShapeFields_toSelection (schema : Schema)
    (fuel : Nat) (parentType : Name) (condition : ResponseShape.Condition)
    (field : LeafField) :
    condition.satisfiableBool = true ->
      ResponseShape.Shape.collectSelectionShapeFields schema (fuel + 1)
        parentType condition field.toSelection
        = [toShapeField condition field] := by
  intro hcondition
  cases condition with
  | mk possibleTypes booleanLiterals =>
      cases possibleTypes with
      | none =>
          cases field
          simp [toSelection, toShapeField, toShapeVariant,
            ResponseShape.Shape.collectSelectionShapeFields,
            ResponseShape.Condition.fromDirectives?,
            ResponseShape.Condition.and, ResponseShape.Condition.empty,
            ResponseShape.Shape.empty, hcondition]
      | some possibleTypes =>
          cases field
          simp [toSelection, toShapeField, toShapeVariant,
            ResponseShape.Shape.collectSelectionShapeFields,
            ResponseShape.Condition.fromDirectives?,
            ResponseShape.Condition.and, ResponseShape.Condition.empty,
            ResponseShape.Shape.empty, hcondition]

theorem collectSelectionSetShapeFields_toSelectionSet (schema : Schema) :
    ∀ (fuel : Nat) (parentType : Name) (condition : ResponseShape.Condition)
      (fields : List LeafField),
      fields.length <= fuel ->
        condition.satisfiableBool = true ->
          responseNamesNodup fields ->
            ResponseShape.Shape.collectSelectionSetShapeFields schema fuel
              parentType condition (toSelectionSet fields)
              = toShapeFields condition fields := by
  intro fuel parentType condition fields
  induction fields generalizing fuel parentType with
  | nil =>
      intro _hfuel _hcondition _hnodup
      cases fuel <;>
        simp [toSelectionSet, toShapeFields,
          ResponseShape.Shape.collectSelectionSetShapeFields]
  | cons field rest ih =>
      intro hfuel hcondition hnodup
      cases fuel with
      | zero =>
          simp at hfuel
      | succ fuel =>
          have hrestFuel : rest.length <= fuel + 1 :=
            Nat.le_trans (Nat.le_of_succ_le_succ hfuel) (Nat.le_succ fuel)
          have hnodupCons := hnodup
          simp [responseNamesNodup, responseNames] at hnodupCons
          rcases hnodupCons with ⟨_hnotMem, hrestNodupRaw⟩
          have hrestNodup : responseNamesNodup rest := by
            simpa [responseNamesNodup, responseNames] using hrestNodupRaw
          have hselection :=
            collectSelectionShapeFields_toSelection schema fuel parentType condition
              field hcondition
          have hrest :=
            ih (fuel + 1) parentType hrestFuel hcondition hrestNodup
          have hrest' :
              ResponseShape.Shape.collectSelectionSetShapeFields schema (fuel + 1)
                parentType condition (List.map toSelection rest)
                = toShapeFields condition rest := by
            simpa [toSelectionSet] using hrest
          have hmerge :
              ResponseShape.Shape.mergeFields
                (toShapeFields condition [field])
                (toShapeFields condition rest)
                = toShapeFields condition ([field] ++ rest) :=
            mergeFields_toShapeFields_append condition [field] rest
              (by simpa [responseNamesNodup] using hnodup)
          have hmerge' :
              ResponseShape.Shape.mergeFields
                [toShapeField condition field]
                (toShapeFields condition rest)
                = toShapeField condition field ::
                  List.map (toShapeField condition) rest := by
            simpa [toShapeFields] using hmerge
          have hmerge'' :
              ResponseShape.Shape.mergeFields
                [toShapeField condition field]
                (List.map (toShapeField condition) rest)
                = toShapeField condition field ::
                  List.map (toShapeField condition) rest := by
            simpa [toShapeFields] using hmerge'
          simp [toSelectionSet, toShapeFields,
            ResponseShape.Shape.collectSelectionSetShapeFields,
            hcondition, hselection, hrest', hmerge'']

theorem collectSelectionSetShapeFields_toSelectionSet_unsat (schema : Schema) :
    ∀ (fuel : Nat) (parentType : Name) (condition : ResponseShape.Condition)
      (fields : List LeafField),
      condition.satisfiableBool = false ->
        ResponseShape.Shape.collectSelectionSetShapeFields schema fuel
          parentType condition (toSelectionSet fields) = [] := by
  intro fuel parentType condition fields
  induction fields generalizing fuel parentType with
  | nil =>
      intro _hcondition
      cases fuel <;>
        simp [toSelectionSet, ResponseShape.Shape.collectSelectionSetShapeFields]
  | cons field rest ih =>
      intro hcondition
      cases fuel with
      | zero =>
          simp [toSelectionSet, ResponseShape.Shape.collectSelectionSetShapeFields]
      | succ fuel =>
          simp [toSelectionSet, ResponseShape.Shape.collectSelectionSetShapeFields,
            hcondition]

theorem ofSemanticOperation_toSelectionSet (schema : Schema)
    (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition) (fields : List LeafField) :
    (ResponseShape.Shape.semanticOperationInitialCondition schema
      { name := name,
        rootType := rootType,
        variableDefinitions := variableDefinitions,
        selectionSet := toSelectionSet fields }).satisfiableBool = true ->
      responseNamesNodup fields ->
        ResponseShape.Shape.ofSemanticOperation schema
          { name := name,
            rootType := rootType,
            variableDefinitions := variableDefinitions,
            selectionSet := toSelectionSet fields }
          =
            ⟨toShapeFields
              (ResponseShape.Shape.semanticOperationInitialCondition schema
                { name := name,
                  rootType := rootType,
                  variableDefinitions := variableDefinitions,
                  selectionSet := toSelectionSet fields })
              fields⟩ := by
  intro hcondition hnodup
  have hfuel : fields.length <= fields.length + 1 := by omega
  simp [ResponseShape.Shape.ofSemanticOperation,
    ResponseShape.Shape.semanticSelectionSetShape,
    ResponseShape.Shape.semanticOperationShapeFuel, Semantic.Operation.size,
    toSelectionSet_size,
    collectSelectionSetShapeFields_toSelectionSet schema (fields.length + 1)
      rootType
      (ResponseShape.Shape.semanticOperationInitialCondition schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := toSelectionSet fields })
      fields hfuel hcondition hnodup]

theorem includesVariantsBool_toShapeVariant_self
    (condition : ResponseShape.Condition) (field : LeafField) :
    ResponseShape.Shape.includesVariantsBool
      [toShapeVariant condition field] [toShapeVariant condition field] = true := by
  simpa [toShapeVariant] using
    ResponseShape.Shape.includesVariantsBool_singleton_empty_self
      (condition, ResponseShape.selectedField field.fieldName field.arguments)

theorem includesFieldsBool_toShapeFields_append_self
    (condition : ResponseShape.Condition) :
    ∀ (shapePrefix suffix : List LeafField),
      responseNamesNodup (shapePrefix ++ suffix) ->
        ResponseShape.Shape.includesFieldsBool
          (toShapeFields condition suffix)
          (toShapeFields condition (shapePrefix ++ suffix)) = true := by
  intro shapePrefix suffix
  induction suffix generalizing shapePrefix with
  | nil =>
      intro _hnodup
      simp [toShapeFields, ResponseShape.Shape.includesFieldsBool]
  | cons field rest ih =>
      intro hnodup
      have hnameParts :
          (responseNames shapePrefix ++ field.responseName :: responseNames rest).Nodup := by
        simpa [responseNamesNodup, responseNames, List.map_append] using hnodup
      simp [List.nodup_append] at hnameParts
      rcases hnameParts with ⟨_hprefix, _hfieldRest, hseparate⟩
      have hnotMemPrefix : field.responseName ∉ responseNames shapePrefix := by
        intro hmem
        exact (hseparate field.responseName hmem).left rfl
      have hlookup :
          ResponseShape.Shape.lookupField field.responseName
            (toShapeFields condition (shapePrefix ++ field :: rest))
            = some [toShapeVariant condition field] :=
        lookupField_toShapeFields_append_cons_self condition shapePrefix field rest
          hnotMemPrefix
      have hlookup' :
          ResponseShape.Shape.lookupField (toShapeField condition field).fst
            (List.map (toShapeField condition) shapePrefix ++
              toShapeField condition field :: List.map (toShapeField condition) rest)
            = some [toShapeVariant condition field] := by
        simpa [toShapeFields, toShapeField] using hlookup
      have hvariants :
          ResponseShape.Shape.includesVariantsBool
            [toShapeVariant condition field] [toShapeVariant condition field] = true :=
        includesVariantsBool_toShapeVariant_self condition field
      have hvariants' :
          ResponseShape.Shape.includesVariantsBool
            (toShapeField condition field).snd [toShapeVariant condition field] = true := by
        simpa [toShapeField] using hvariants
      have hrestNodup : responseNamesNodup ((shapePrefix ++ [field]) ++ rest) := by
        simpa [responseNamesNodup, responseNames, List.map_append,
          List.append_assoc] using hnodup
      have hrest :=
        ih (shapePrefix ++ [field]) hrestNodup
      have hrest' :
          ResponseShape.Shape.includesFieldsBool
            (toShapeFields condition rest)
            (toShapeFields condition (shapePrefix ++ field :: rest)) = true := by
        simpa [List.append_assoc] using hrest
      have hrest'' :
          ResponseShape.Shape.includesFieldsBool
            (List.map (toShapeField condition) rest)
            (List.map (toShapeField condition) shapePrefix ++
              toShapeField condition field :: List.map (toShapeField condition) rest)
            = true := by
        simpa [toShapeFields] using hrest'
      simp [toShapeFields, ResponseShape.Shape.includesFieldsBool,
        hlookup', hvariants', hrest'']

theorem includesBool_toShapeFields_self
    (condition : ResponseShape.Condition) (fields : List LeafField) :
    responseNamesNodup fields ->
      ResponseShape.Shape.includesBool
        ⟨toShapeFields condition fields⟩
        ⟨toShapeFields condition fields⟩ = true := by
  intro hnodup
  simpa [ResponseShape.Shape.includesBool] using
    includesFieldsBool_toShapeFields_append_self condition [] fields hnodup

theorem equivalentBool_toShapeFields_self
    (condition : ResponseShape.Condition) (fields : List LeafField) :
    responseNamesNodup fields ->
      ResponseShape.Shape.equivalentBool
        ⟨toShapeFields condition fields⟩
        ⟨toShapeFields condition fields⟩ = true := by
  intro hnodup
  simp [ResponseShape.Shape.equivalentBool,
    includesBool_toShapeFields_self condition fields hnodup]

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

namespace LeafField

theorem typedResponseFieldConformsToShapeVariant
    (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues)
    (shapeFuel executionFuel : Nat) (parentType runtimeType : Name)
    (source : Value) (condition : ResponseShape.Condition)
    (field : LeafField) :
    conditionHoldsBool variableValues runtimeType condition = true ->
      typedVariantConformsToShapeBool variableValues (shapeFuel + 1) runtimeType
        (TypedExecution.completeValue schema store variableValues executionFuel
          ((schema.fieldReturnType? parentType field.fieldName).getD field.fieldName) []
          (store.resolveValue field.fieldName field.arguments source))
        [toShapeVariant condition field] = true := by
  intro hcondition
  have hchild :
      typedResponseConformsToShapeBool variableValues shapeFuel
        (TypedExecution.completeValue schema store variableValues executionFuel
          ((schema.fieldReturnType? parentType field.fieldName).getD field.fieldName) []
          (store.resolveValue field.fieldName field.arguments source))
        ResponseShape.Shape.empty = true :=
    typedResponseConformsToShapeBool_completeValue_emptySelection_emptyWithFuel
      schema store variableValues shapeFuel executionFuel
      ((schema.fieldReturnType? parentType field.fieldName).getD field.fieldName)
      (store.resolveValue field.fieldName field.arguments source)
  simpa [toShapeVariant, variantHeaderActiveBool] using
    typedVariantConformsToShapeBool_singleton variableValues shapeFuel runtimeType
      (TypedExecution.completeValue schema store variableValues executionFuel
        ((schema.fieldReturnType? parentType field.fieldName).getD field.fieldName) []
        (store.resolveValue field.fieldName field.arguments source))
      (condition, ResponseShape.selectedField field.fieldName field.arguments)
      ResponseShape.Shape.empty hcondition hchild

theorem typedFieldsConformToShapeFields_append
    (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues) (executionFuel : Nat)
    (parentType runtimeType : Name) (source : Value)
    (condition : ResponseShape.Condition) :
    ∀ (shapePrefix suffix : List LeafField),
      responseNamesNodup (shapePrefix ++ suffix) ->
        conditionHoldsBool variableValues runtimeType condition = true ->
          typedFieldsConformToShapeBool variableValues suffix.length runtimeType
            (typedResponseFields schema store variableValues executionFuel parentType
              source suffix)
            ⟨toShapeFields condition (shapePrefix ++ suffix)⟩ = true := by
  intro shapePrefix suffix
  induction suffix generalizing shapePrefix with
  | nil =>
      intro _hnodup _hcondition
      simp [typedResponseFields, typedFieldsConformToShapeBool]
  | cons field rest ih =>
      intro hnodup hcondition
      have hnameParts :
          (responseNames shapePrefix ++ field.responseName :: responseNames rest).Nodup := by
        simpa [responseNamesNodup, responseNames, List.map_append] using hnodup
      simp [List.nodup_append] at hnameParts
      rcases hnameParts with ⟨_hprefix, _hfieldRest, hseparate⟩
      have hnotMemPrefix : field.responseName ∉ responseNames shapePrefix := by
        intro hmem
        exact (hseparate field.responseName hmem).left rfl
      have hlookup :
          ResponseShape.Shape.lookupField field.responseName
            (toShapeFields condition (shapePrefix ++ field :: rest))
            = some [toShapeVariant condition field] :=
        lookupField_toShapeFields_append_cons_self condition shapePrefix field rest
          hnotMemPrefix
      have hvariant :
          typedVariantConformsToShapeBool variableValues rest.length runtimeType
            (TypedExecution.completeValue schema store variableValues executionFuel
              ((schema.fieldReturnType? parentType field.fieldName).getD field.fieldName)
              [] (store.resolveValue field.fieldName field.arguments source))
            [toShapeVariant condition field] = true := by
        cases hfuel : rest.length with
        | zero =>
            simp [typedVariantConformsToShapeBool]
        | succ shapeFuel =>
            simpa [hfuel] using
              typedResponseFieldConformsToShapeVariant schema store variableValues
                shapeFuel executionFuel parentType runtimeType source condition field
                hcondition
      have hrestNodup : responseNamesNodup ((shapePrefix ++ [field]) ++ rest) := by
        simpa [responseNamesNodup, responseNames, List.map_append,
          List.append_assoc] using hnodup
      have hrest :=
        ih (shapePrefix ++ [field]) hrestNodup hcondition
      have hrest' :
          typedFieldsConformToShapeBool variableValues rest.length runtimeType
            (typedResponseFields schema store variableValues executionFuel parentType
              source rest)
            ⟨toShapeFields condition (shapePrefix ++ field :: rest)⟩ = true := by
        simpa [List.append_assoc] using hrest
      have hrest'' :
          typedFieldsConformToShapeBool variableValues rest.length runtimeType
            (List.map
              (typedResponseField schema store variableValues executionFuel parentType
                source)
              rest)
            ⟨toShapeFields condition (shapePrefix ++ field :: rest)⟩ = true := by
        simpa [typedResponseFields] using hrest'
      simp [typedResponseFields, typedResponseField, typedFieldsConformToShapeBool,
        hlookup, hvariant, hrest'']

theorem typedFieldsConformToShapeFields
    (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues) (executionFuel : Nat)
    (parentType runtimeType : Name) (source : Value)
    (condition : ResponseShape.Condition) (fields : List LeafField) :
    responseNamesNodup fields ->
      conditionHoldsBool variableValues runtimeType condition = true ->
        typedFieldsConformToShapeBool variableValues fields.length runtimeType
          (typedResponseFields schema store variableValues executionFuel parentType
            source fields)
          ⟨toShapeFields condition fields⟩ = true := by
  intro hnodup hcondition
  simpa using
    typedFieldsConformToShapeFields_append schema store variableValues executionFuel
      parentType runtimeType source condition [] fields hnodup hcondition

end LeafField

theorem groundNormalFormCorrect_twoSameLeafNoDirectives (schema : Schema)
    (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (responseName fieldName : Name) (arguments : List Argument) :
    groundNormalFormCorrect schema
      { name := name,
        rootType := rootType,
        variableDefinitions := variableDefinitions,
        selectionSet := [
          .field responseName fieldName arguments [] [],
          .field responseName fieldName arguments [] []
        ] } := by
  rw [groundNormalFormCorrect]
  rw [NormalForm.normalizeSemanticOperation_twoSameLeafNoDirectives]
  intro store variableValues root _hstore _hroot
  simp [executeSemanticQueryWithFuel, Execution.executeSemanticQueryFuel,
    Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
    Execution.executeSelectionSet, Execution.collectFields, Execution.collectSelection,
    Execution.selectionDirectivesAllowBool, Execution.mergeExecutableGroups,
    Execution.addExecutableGroup, Execution.addExecutableFields,
    Execution.addExecutableField, Execution.executeCollectedFields,
    Execution.executeField, Execution.mergedFieldSelectionSet]

theorem groundNormalFormCorrect_twoSameCompositeDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName : Name) (parentArguments : List Argument)
    (leftResponseName leftFieldName : Name) (leftArguments : List Argument)
    (rightResponseName rightFieldName : Name) (rightArguments : List Argument) :
    leftResponseName ≠ rightResponseName ->
      groundNormalFormCorrect schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [
            .field parentResponseName parentFieldName parentArguments [] [
              .field leftResponseName leftFieldName leftArguments [] []
            ],
            .field parentResponseName parentFieldName parentArguments [] [
              .field rightResponseName rightFieldName rightArguments [] []
            ]
          ] } := by
  intro hdistinct
  rw [groundNormalFormCorrect]
  rw [NormalForm.normalizeSemanticOperation_twoSameCompositeDistinctLeafNoDirectives
    schema name rootType variableDefinitions parentResponseName parentFieldName
    parentArguments leftResponseName leftFieldName leftArguments rightResponseName
    rightFieldName rightArguments hdistinct]
  intro store variableValues root _hstore _hroot
  simp [executeSemanticQueryWithFuel, Execution.executeSemanticQueryFuel,
    Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
    Execution.executeSelectionSet, Execution.collectFields, Execution.collectSelection,
    Execution.selectionDirectivesAllowBool, Execution.mergeExecutableGroups,
    Execution.addExecutableGroup, Execution.addExecutableFields,
    Execution.addExecutableField, Execution.executeCollectedFields,
    Execution.executeField, Execution.mergedFieldSelectionSet]

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
      ResponseShape.VariantHeader.eqBool_self,
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
theorem normalFormPreservesResponseShapeBool_twoSameLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (responseName fieldName : Name) (arguments : List Argument) :
    normalFormPreservesResponseShapeBool schema
      { name := name,
        rootType := rootType,
        variableDefinitions := variableDefinitions,
        selectionSet := [
          .field responseName fieldName arguments [] [],
          .field responseName fieldName arguments [] []
        ] } = true := by
  rw [normalFormPreservesResponseShapeBool]
  rw [NormalForm.normalizeSemanticOperation_twoSameLeafNoDirectives]
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
      hempty, ResponseShape.Shape.mergeFields, ResponseShape.Shape.merge,
      ResponseShape.Shape.size, ResponseShape.Shape.fieldsSize,
      ResponseShape.Shape.variantsSize, ResponseShape.Shape.mergeWithFuel,
      ResponseShape.Shape.mergeFieldsWithFuel, ResponseShape.Shape.mergeVariantsWithFuel,
      ResponseShape.Shape.mergeFields_singleton_empty_self,
      ResponseShape.Shape.equivalentBool, ResponseShape.Shape.includesBool,
      ResponseShape.Shape.includesFieldsBool, ResponseShape.Shape.includesVariantsBool,
      ResponseShape.Shape.lookupField, ResponseShape.Shape.lookupIncludingVariant,
      ResponseShape.VariantHeader.eqBool_self,
      ResponseShape.VariantHeader.includedByBool_self,
      ResponseShape.Shape.empty_includesBool]

theorem normalFormPreservesResponseShape_twoSameLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (responseName fieldName : Name) (arguments : List Argument) :
    normalFormPreservesResponseShape schema
      { name := name,
        rootType := rootType,
        variableDefinitions := variableDefinitions,
        selectionSet := [
          .field responseName fieldName arguments [] [],
          .field responseName fieldName arguments [] []
        ] } := by
  exact normalFormPreservesResponseShapeBool_sound schema _
    (normalFormPreservesResponseShapeBool_twoSameLeafNoDirectives schema name rootType
      variableDefinitions responseName fieldName arguments)

theorem normalFormPreservesResponseShapeBool_distinctLeafFieldsNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition) (fields : List LeafField) :
    LeafField.responseNamesNodup fields ->
      normalFormPreservesResponseShapeBool schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := LeafField.toSelectionSet fields } = true := by
  intro hnodup
  let operation : Semantic.Operation :=
    { name := name,
      rootType := rootType,
      variableDefinitions := variableDefinitions,
      selectionSet := LeafField.toSelectionSet fields }
  rw [normalFormPreservesResponseShapeBool]
  rw [LeafField.normalizeSemanticOperation_toSelectionSet schema name rootType
    variableDefinitions fields hnodup]
  by_cases hcondition :
      ResponseShape.Condition.satisfiableBool
        (ResponseShape.Shape.semanticOperationInitialCondition schema operation) = true
  · have hshape :
        ResponseShape.Shape.ofSemanticOperation schema operation =
          ⟨LeafField.toShapeFields
            (ResponseShape.Shape.semanticOperationInitialCondition schema operation)
            fields⟩ := by
      simpa [operation] using
        LeafField.ofSemanticOperation_toSelectionSet schema name rootType variableDefinitions
          fields hcondition hnodup
    rw [hshape]
    exact LeafField.equivalentBool_toShapeFields_self
      (ResponseShape.Shape.semanticOperationInitialCondition schema operation)
      fields hnodup
  · have hconditionFalse :
        ResponseShape.Condition.satisfiableBool
          (ResponseShape.Shape.semanticOperationInitialCondition schema operation) = false := by
      cases h :
          ResponseShape.Condition.satisfiableBool
            (ResponseShape.Shape.semanticOperationInitialCondition schema operation) <;>
        simp [h] at hcondition ⊢
    have hshape :
        ResponseShape.Shape.ofSemanticOperation schema operation =
          ResponseShape.Shape.empty := by
      have hcollect :
          ResponseShape.Shape.collectSelectionSetShapeFields schema (fields.length + 1)
            rootType (ResponseShape.Shape.semanticOperationInitialCondition schema operation)
            (LeafField.toSelectionSet fields) = [] :=
        LeafField.collectSelectionSetShapeFields_toSelectionSet_unsat schema
          (fields.length + 1) rootType
          (ResponseShape.Shape.semanticOperationInitialCondition schema operation)
          fields hconditionFalse
      simp [operation, ResponseShape.Shape.ofSemanticOperation,
        ResponseShape.Shape.semanticOperationShapeFuel, Semantic.Operation.size,
        LeafField.toSelectionSet_size, ResponseShape.Shape.semanticSelectionSetShape,
        hcollect, ResponseShape.Shape.empty]
    rw [hshape]
    exact ResponseShape.Shape.empty_equivalentBool

theorem normalFormPreservesResponseShape_distinctLeafFieldsNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition) (fields : List LeafField) :
    LeafField.responseNamesNodup fields ->
      normalFormPreservesResponseShape schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := LeafField.toSelectionSet fields } := by
  intro hnodup
  exact normalFormPreservesResponseShapeBool_sound schema _
    (normalFormPreservesResponseShapeBool_distinctLeafFieldsNoDirectives schema name rootType
      variableDefinitions fields hnodup)

set_option linter.unusedSimpArgs false in
theorem responseShapeCorrectForTypedExecutionAtRoot_twoSameLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (responseName fieldName : Name) (arguments : List Argument) :
    responseShapeCorrectForTypedExecutionAtRoot schema
      { name := name,
        rootType := rootType,
        variableDefinitions := variableDefinitions,
        selectionSet := [
          .field responseName fieldName arguments [] [],
          .field responseName fieldName arguments [] []
        ] } := by
  intro store variableValues root _hstore _hroot hrootType
  have hrootType' : schema.typeIncludesObject rootType root.typeName := hrootType
  have hnonempty : ¬ schema.getPossibleTypes rootType = [] :=
    possibleTypes_nonempty_of_typeIncludesObject schema hrootType'
  simp [TypedExecution.executeSemanticQuery, Execution.executeSemanticQueryFuel,
    Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
    TypedExecution.executeSelectionSet, Execution.collectFields, Execution.collectSelection,
    Execution.selectionDirectivesAllowBool, Execution.mergeExecutableGroups,
    Execution.addExecutableGroup, Execution.addExecutableFields,
    Execution.addExecutableField, TypedExecution.executeCollectedFields,
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
    ResponseShape.Shape.mergeFieldsWithFuel, ResponseShape.Shape.mergeVariantsWithFuel,
    ResponseShape.VariantHeader.eqBool_self, typedResponseConformsToShapeBool,
    typedFieldsConformToShapeBool, typedVariantConformsToShapeBool,
    ResponseShape.Shape.lookupField]

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

theorem responseShapeCorrectForTypedExecutionAtRoot_distinctLeafFieldsNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition) (fields : List LeafField) :
    LeafField.responseNamesNodup fields ->
      responseShapeCorrectForTypedExecutionAtRoot schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := LeafField.toSelectionSet fields } := by
  intro hnodup store variableValues root _hstore _hroot hrootType
  let operation : Semantic.Operation :=
    { name := name,
      rootType := rootType,
      variableDefinitions := variableDefinitions,
      selectionSet := LeafField.toSelectionSet fields }
  have hrootType' : schema.typeIncludesObject rootType root.typeName := hrootType
  have hnonempty : ¬ schema.getPossibleTypes rootType = [] :=
    possibleTypes_nonempty_of_typeIncludesObject schema hrootType'
  have hconditionSat :
      ResponseShape.Condition.satisfiableBool
        (ResponseShape.Shape.semanticOperationInitialCondition schema operation) = true := by
    simp [operation, ResponseShape.Shape.semanticOperationInitialCondition,
      ResponseShape.Condition.satisfiableBool,
      ResponseShape.Condition.hasContradictionBool,
      ResponseShape.Condition.possibleTypesEmptyBool,
      ResponseShape.BooleanLiteral.hasContradictionBool, hnonempty]
  have hconditionHolds :
      conditionHoldsBool variableValues root.typeName
        (ResponseShape.Shape.semanticOperationInitialCondition schema operation) = true :=
    semanticOperationInitialCondition_holds schema variableValues operation hrootType'
  have hexec :
      TypedExecution.executeSemanticQuery schema store variableValues operation root
        =
          .object root.typeName
            (LeafField.typedResponseFields schema store variableValues
              (fields.length * 3) rootType (.object root.typeName root.id) fields) := by
    simpa [operation] using
      LeafField.executeSemanticQuery_toSelectionSet schema store variableValues name rootType
        variableDefinitions fields root hnodup
  have hshape :
      ResponseShape.Shape.ofSemanticOperation schema operation
        =
          ⟨LeafField.toShapeFields
            (ResponseShape.Shape.semanticOperationInitialCondition schema operation)
            fields⟩ := by
    simpa [operation] using
      LeafField.ofSemanticOperation_toSelectionSet schema name rootType variableDefinitions
        fields hconditionSat hnodup
  rw [hexec, hshape]
  simp [operation, Semantic.Operation.size, LeafField.toSelectionSet_size,
    typedResponseConformsToShapeBool]
  exact LeafField.typedFieldsConformToShapeFields schema store variableValues
    (fields.length * 3) rootType root.typeName (.object root.typeName root.id)
    (ResponseShape.Shape.semanticOperationInitialCondition schema operation)
    fields hnodup hconditionHolds

end DataModel

end GraphQL
