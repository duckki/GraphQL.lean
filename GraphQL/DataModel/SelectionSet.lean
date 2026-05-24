import GraphQL.DataModel.Store

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

@[simp]
theorem toSelectionSet_append (leftFields rightFields : List LeafField) :
    toSelectionSet (leftFields ++ rightFields)
      = toSelectionSet leftFields ++ toSelectionSet rightFields := by
  simp [toSelectionSet, List.map_append]

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

theorem mergeWithFuel_parentVariant_childShapeFields_append
    (fuel : Nat) (parentResponseName : Name)
    (parentHeader : ResponseShape.VariantHeader)
    (childCondition : ResponseShape.Condition) (leftFields rightFields : List LeafField) :
    rightFields.length + 4 <= fuel ->
      responseNamesNodup (leftFields ++ rightFields) ->
        (ResponseShape.Shape.mergeWithFuel fuel
          ⟨[(parentResponseName,
            [(parentHeader, ⟨toShapeFields childCondition leftFields⟩)])]⟩
          ⟨[(parentResponseName,
            [(parentHeader, ⟨toShapeFields childCondition rightFields⟩)])]⟩).fields
        =
          [(parentResponseName,
            [(parentHeader,
              ⟨toShapeFields childCondition (leftFields ++ rightFields)⟩)])] := by
  intro hfuel hnodup
  cases fuel with
  | zero =>
      omega
  | succ fuel =>
      cases fuel with
      | zero =>
          omega
      | succ fuel =>
          cases fuel with
          | zero =>
              omega
          | succ fuel =>
              cases fuel with
              | zero =>
                  omega
              | succ childFuel =>
                  have hchildFuel : rightFields.length <= childFuel := by
                    omega
                  have hchildren :
                      ResponseShape.Shape.mergeFieldsWithFuel childFuel
                        (toShapeFields childCondition leftFields)
                        (toShapeFields childCondition rightFields)
                        = toShapeFields childCondition (leftFields ++ rightFields) :=
                    mergeFieldsWithFuel_toShapeFields_append childCondition childFuel
                      leftFields rightFields hchildFuel hnodup
                  simp [ResponseShape.Shape.mergeWithFuel,
                    ResponseShape.Shape.mergeFieldsWithFuel,
                    ResponseShape.Shape.mergeVariantsWithFuel,
                    ResponseShape.VariantHeader.eqBool_self, hchildren]

theorem mergeFields_parentVariant_childShapeFields_append
    (parentResponseName : Name) (parentHeader : ResponseShape.VariantHeader)
    (childCondition : ResponseShape.Condition) (leftFields rightFields : List LeafField) :
    responseNamesNodup (leftFields ++ rightFields) ->
      ResponseShape.Shape.mergeFields
        [(parentResponseName,
          [(parentHeader, ⟨toShapeFields childCondition leftFields⟩)])]
        [(parentResponseName,
          [(parentHeader, ⟨toShapeFields childCondition rightFields⟩)])]
        =
          [(parentResponseName,
            [(parentHeader,
              ⟨toShapeFields childCondition (leftFields ++ rightFields)⟩)])] := by
  intro hnodup
  have hfuel :
      rightFields.length + 4 <=
        ResponseShape.Shape.size
          ⟨[(parentResponseName,
            [(parentHeader, ⟨toShapeFields childCondition leftFields⟩)])]⟩
        + ResponseShape.Shape.size
          ⟨[(parentResponseName,
            [(parentHeader, ⟨toShapeFields childCondition rightFields⟩)])]⟩ := by
    simp [ResponseShape.Shape.size, ResponseShape.Shape.fieldsSize,
      ResponseShape.Shape.variantsSize, shapeFieldsSize_toShapeFields]
    omega
  simpa [ResponseShape.Shape.mergeFields, ResponseShape.Shape.merge] using
    mergeWithFuel_parentVariant_childShapeFields_append
      (ResponseShape.Shape.size
          ⟨[(parentResponseName,
            [(parentHeader, ⟨toShapeFields childCondition leftFields⟩)])]⟩
        + ResponseShape.Shape.size
          ⟨[(parentResponseName,
            [(parentHeader, ⟨toShapeFields childCondition rightFields⟩)])]⟩)
      parentResponseName parentHeader childCondition leftFields rightFields hfuel hnodup

theorem mergeFields_parentVariant_childShape_nil
    (parentResponseName : Name) (parentHeader : ResponseShape.VariantHeader)
    (childShape : ResponseShape.Shape) :
    ResponseShape.Shape.mergeFields
      [(parentResponseName, [(parentHeader, childShape)])] []
      = [(parentResponseName, [(parentHeader, childShape)])] := by
  simp [ResponseShape.Shape.mergeFields, ResponseShape.Shape.merge,
    ResponseShape.Shape.size, ResponseShape.Shape.fieldsSize,
    ResponseShape.Shape.variantsSize, ResponseShape.Shape.mergeWithFuel]
  cases childShape.size <;> rfl

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
  simpa using
    mergeFields_parentVariant_childShapeFields_append parentResponseName parentHeader
      childCondition [left] [right] (by
        simp [responseNamesNodup, responseNames, hdistinct])

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

theorem childShape_toSelectionSet (schema : Schema)
    (fuel : Nat) (parentType : Name) (condition : ResponseShape.Condition)
    (fields : List LeafField) :
    fields.length <= fuel ->
      condition.satisfiableBool = true ->
      responseNamesNodup fields ->
        (match toSelectionSet fields with
        | [] => ResponseShape.Shape.empty
        | _ =>
            ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema fuel
              parentType condition (toSelectionSet fields)⟩)
          = ⟨toShapeFields condition fields⟩ := by
  intro hfuel hcondition hnodup
  cases fields with
  | nil =>
      simp [toSelectionSet, toShapeFields, ResponseShape.Shape.empty]
  | cons field rest =>
      have hcollect :
          ResponseShape.Shape.collectSelectionSetShapeFields schema fuel parentType
            condition (toSelectionSet (field :: rest))
          = toShapeFields condition (field :: rest) :=
        collectSelectionSetShapeFields_toSelectionSet schema fuel parentType condition
          (field :: rest) hfuel hcondition hnodup
      simpa [toSelectionSet] using hcollect

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

theorem childShape_toSelectionSet_unsat (schema : Schema)
    (fuel : Nat) (parentType : Name) (condition : ResponseShape.Condition)
    (fields : List LeafField) :
    condition.satisfiableBool = false ->
      (match toSelectionSet fields with
      | [] => ResponseShape.Shape.empty
      | _ =>
          ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema fuel
            parentType condition (toSelectionSet fields)⟩)
        = ResponseShape.Shape.empty := by
  intro hcondition
  cases fields with
  | nil =>
      simp [toSelectionSet, ResponseShape.Shape.empty]
  | cons field rest =>
      have hcollect :
          ResponseShape.Shape.collectSelectionSetShapeFields schema fuel parentType
            condition (toSelectionSet (field :: rest)) = [] :=
        collectSelectionSetShapeFields_toSelectionSet_unsat schema fuel parentType
          condition (field :: rest) hcondition
      have hcollect' :
          ResponseShape.Shape.collectSelectionSetShapeFields schema fuel parentType
            condition (field.toSelection :: List.map toSelection rest) = [] := by
        simpa [toSelectionSet] using hcollect
      simp [toSelectionSet, hcollect', ResponseShape.Shape.empty]

@[simp]
theorem condition_and_empty (condition : ResponseShape.Condition) :
    condition.and ResponseShape.Condition.empty = condition := by
  cases condition with
  | mk possibleTypes booleanLiterals =>
      cases possibleTypes <;>
        simp [ResponseShape.Condition.and, ResponseShape.Condition.empty]

theorem collectSelectionShapeFields_field_toSelectionSet (schema : Schema)
    (fuel : Nat) (parentType : Name) (condition : ResponseShape.Condition)
    (responseName fieldName : Name) (arguments : List Argument)
    (fields : List LeafField) :
    let childType := (schema.fieldReturnType? parentType fieldName).getD fieldName
    let childCondition := ResponseShape.Condition.forChildType schema condition childType
    condition.satisfiableBool = true ->
      childCondition.satisfiableBool = true ->
        fields.length <= fuel ->
          responseNamesNodup fields ->
            ResponseShape.Shape.collectSelectionShapeFields schema (fuel + 1)
              parentType condition
              (.field responseName fieldName arguments [] (toSelectionSet fields))
            =
              [(responseName,
                [((condition, ResponseShape.selectedField fieldName arguments),
                  ⟨toShapeFields childCondition fields⟩)])] := by
  intro childType childCondition hcondition hchildCondition hfuel hnodup
  have hchildShape :
      (match toSelectionSet fields with
      | [] => ResponseShape.Shape.empty
      | _ =>
          ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema fuel childType
            childCondition (toSelectionSet fields)⟩)
        = ⟨toShapeFields childCondition fields⟩ :=
    childShape_toSelectionSet schema fuel childType childCondition fields
      hfuel hchildCondition hnodup
  simp [ResponseShape.Shape.collectSelectionShapeFields,
    ResponseShape.Condition.fromDirectives?, hcondition]
  simpa [childType, childCondition] using hchildShape

theorem collectSelectionShapeFields_field_toSelectionSet_unsat (schema : Schema)
    (fuel : Nat) (parentType : Name) (condition : ResponseShape.Condition)
    (responseName fieldName : Name) (arguments : List Argument)
    (fields : List LeafField) :
    let childType := (schema.fieldReturnType? parentType fieldName).getD fieldName
    let childCondition := ResponseShape.Condition.forChildType schema condition childType
    condition.satisfiableBool = true ->
      childCondition.satisfiableBool = false ->
        ResponseShape.Shape.collectSelectionShapeFields schema (fuel + 1)
          parentType condition
          (.field responseName fieldName arguments [] (toSelectionSet fields))
        =
          [(responseName,
            [((condition, ResponseShape.selectedField fieldName arguments),
              ResponseShape.Shape.empty)])] := by
  intro childType childCondition hcondition hchildCondition
  have hchildShape :
      (match toSelectionSet fields with
      | [] => ResponseShape.Shape.empty
      | _ =>
          ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema fuel childType
            childCondition (toSelectionSet fields)⟩)
        = ResponseShape.Shape.empty :=
    childShape_toSelectionSet_unsat schema fuel childType childCondition fields
      hchildCondition
  simp [ResponseShape.Shape.collectSelectionShapeFields,
    ResponseShape.Condition.fromDirectives?, hcondition]
  simpa [childType, childCondition] using hchildShape

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

theorem equivalentBool_parentVariant_childShapeFields_self
    (parentResponseName : Name) (parentHeader : ResponseShape.VariantHeader)
    (childCondition : ResponseShape.Condition) (fields : List LeafField) :
    responseNamesNodup fields ->
      ResponseShape.Shape.equivalentBool
        ⟨[(parentResponseName,
          [(parentHeader, ⟨toShapeFields childCondition fields⟩)])]⟩
        ⟨[(parentResponseName,
          [(parentHeader, ⟨toShapeFields childCondition fields⟩)])]⟩ = true := by
  intro hnodup
  have hchild :
      ResponseShape.Shape.includesFieldsBool
        (toShapeFields childCondition fields)
        (toShapeFields childCondition fields) = true := by
    simpa [ResponseShape.Shape.includesBool] using
      includesBool_toShapeFields_self childCondition fields hnodup
  simp [ResponseShape.Shape.equivalentBool, ResponseShape.Shape.includesBool,
    ResponseShape.Shape.includesFieldsBool, ResponseShape.Shape.includesVariantsBool,
    ResponseShape.Shape.lookupField, ResponseShape.Shape.lookupIncludingVariant,
    ResponseShape.VariantHeader.includedByBool_self, hchild]

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

theorem normalizeSemanticOperation_twoSameCompositeLeafFieldsNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName : Name) (parentArguments : List Argument)
    (leftFields rightFields : List LeafField) :
    responseNamesNodup (leftFields ++ rightFields) ->
      NormalForm.normalizeSemanticOperation schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [
            .field parentResponseName parentFieldName parentArguments []
              (toSelectionSet leftFields),
            .field parentResponseName parentFieldName parentArguments []
              (toSelectionSet rightFields)
          ] }
        = { name := name,
            rootType := rootType,
            variableDefinitions := variableDefinitions,
            selectionSet := [
              .field parentResponseName parentFieldName parentArguments []
                (toSelectionSet (leftFields ++ rightFields))
            ] } := by
  intro hnodup
  let childFuel := leftFields.length + rightFields.length + 1
  have hchildFuel :
      (leftFields ++ rightFields).length <= childFuel := by
    simp [childFuel]
  have hnormalizeChild :
      ∀ childType,
        NormalForm.normalizeSelectionSet schema
          childFuel childType
          (toSelectionSet leftFields ++ toSelectionSet rightFields)
          = toSelectionSet (leftFields ++ rightFields) := by
    intro childType
    simpa [toSelectionSet_append] using
      normalizeSelectionSet_toSelectionSet schema
        childFuel childType
        (leftFields ++ rightFields) hchildFuel hnodup
  cases hparent : schema.fieldReturnType? rootType parentFieldName with
  | none =>
      rw [NormalForm.normalizeSemanticOperation]
      simp [Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
        toSelectionSet_size]
      rw [show 1 + leftFields.length + (1 + rightFields.length) = childFuel + 1 by
        simp [childFuel]
        omega]
      rw [NormalForm.normalizeSelectionSet]
      change
        NormalForm.mergeFieldSelections.normalizeSelectionSet schema (childFuel + 1)
          rootType
          [
            Semantic.Selection.field parentResponseName parentFieldName parentArguments []
              (toSelectionSet leftFields),
            Semantic.Selection.field parentResponseName parentFieldName parentArguments []
              (toSelectionSet rightFields)
          ]
        =
          [
            Semantic.Selection.field parentResponseName parentFieldName parentArguments []
              (toSelectionSet leftFields ++ toSelectionSet rightFields)
          ]
      simp [childFuel, hparent, NormalForm.mergeFieldSelections.normalizeSelectionSet,
        NormalForm.mergeFieldSelections, Semantic.SelectionSet.fieldsWithResponseName,
        Semantic.SelectionSet.withoutFieldsWithResponseName,
        Semantic.SelectionSet.mergeSelectionSets, Semantic.Selection.responseName?,
        Semantic.Selection.subselections]
  | some childType =>
      rw [NormalForm.normalizeSemanticOperation]
      simp [Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
        toSelectionSet_size]
      rw [show 1 + leftFields.length + (1 + rightFields.length) = childFuel + 1 by
        simp [childFuel]
        omega]
      rw [NormalForm.normalizeSelectionSet]
      change
        NormalForm.mergeFieldSelections.normalizeSelectionSet schema (childFuel + 1)
          rootType
          [
            Semantic.Selection.field parentResponseName parentFieldName parentArguments []
              (toSelectionSet leftFields),
            Semantic.Selection.field parentResponseName parentFieldName parentArguments []
              (toSelectionSet rightFields)
          ]
        =
          [
            Semantic.Selection.field parentResponseName parentFieldName parentArguments []
              (toSelectionSet leftFields ++ toSelectionSet rightFields)
          ]
      simp [childFuel, hparent, NormalForm.mergeFieldSelections.normalizeSelectionSet,
        NormalForm.mergeFieldSelections, Semantic.SelectionSet.fieldsWithResponseName,
        Semantic.SelectionSet.withoutFieldsWithResponseName,
        Semantic.SelectionSet.mergeSelectionSets, Semantic.Selection.responseName?,
        Semantic.Selection.subselections]
      simpa [childFuel, toSelectionSet_append] using hnormalizeChild childType

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

theorem typedResponseConformsToShapeBool_completeValue_namedComposite_oneFuel
    (schema : Schema) (store : Store) (variableValues : Execution.VariableValues)
    (executionFuel : Nat) (parentType childType : Name)
    (selectionSet : List Semantic.Selection) (shape : ResponseShape.Shape)
    (value : Value) :
    Value.conformsToType schema value (.named childType) ->
      ¬ schema.getPossibleTypes childType = [] ->
        typedResponseConformsToShapeBool variableValues 1
          (TypedExecution.completeValue schema store variableValues executionFuel
            parentType selectionSet value)
          shape = true := by
  intro hconforms hchildNonempty
  cases value with
  | null =>
      cases executionFuel <;>
        simp [TypedExecution.completeValue, shallowTypedResponse,
          typedResponseConformsToShapeBool]
  | scalar scalarValue =>
      exact False.elim
        ((scalar_not_conformsToType_of_possibleTypes_nonempty schema scalarValue
          (.named childType) (by simpa [TypeRef.namedType] using hchildNonempty))
          hconforms)
  | object runtimeType id =>
      cases executionFuel <;>
        simp [TypedExecution.completeValue, shallowTypedResponse,
          typedResponseConformsToShapeBool, typedFieldsConformToShapeBool]
  | list values =>
      cases hconforms

theorem typedResponseConformsToShapeBool_completeValue_namedComposite_listOneFuel
    (schema : Schema) (store : Store) (variableValues : Execution.VariableValues)
    (executionFuel : Nat) (parentType childType : Name)
    (selectionSet : List Semantic.Selection) (shape : ResponseShape.Shape)
    (values : List Value) :
    (∀ value, value ∈ values -> Value.conformsToType schema value (.named childType)) ->
      ¬ schema.getPossibleTypes childType = [] ->
        (values.map
          (TypedExecution.completeValue schema store variableValues executionFuel
            parentType selectionSet)).all
          (fun response =>
            typedResponseConformsToShapeBool variableValues 1 response shape) = true := by
  intro hconforms hchildNonempty
  induction values with
  | nil =>
      simp
  | cons value rest ih =>
      have hvalue :
          typedResponseConformsToShapeBool variableValues 1
            (TypedExecution.completeValue schema store variableValues executionFuel
              parentType selectionSet value)
            shape = true :=
        typedResponseConformsToShapeBool_completeValue_namedComposite_oneFuel
          schema store variableValues executionFuel parentType childType selectionSet
          shape value (hconforms value (by simp)) hchildNonempty
      have hrestConforms :
          ∀ value, value ∈ rest ->
            Value.conformsToType schema value (.named childType) := by
        intro restValue hmem
        exact hconforms restValue (by simp [hmem])
      have hrest := ih hrestConforms
      simp [hvalue, hrest]

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

theorem typedFieldsConformToShapeFieldsWithFuel_append
    (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues) (executionFuel : Nat)
    (parentType runtimeType : Name) (source : Value)
    (condition : ResponseShape.Condition) :
    ∀ (shapeFuel : Nat) (shapePrefix suffix : List LeafField),
      responseNamesNodup (shapePrefix ++ suffix) ->
        conditionHoldsBool variableValues runtimeType condition = true ->
          typedFieldsConformToShapeBool variableValues shapeFuel runtimeType
            (typedResponseFields schema store variableValues executionFuel parentType
              source suffix)
            ⟨toShapeFields condition (shapePrefix ++ suffix)⟩ = true := by
  intro shapeFuel
  induction shapeFuel with
  | zero =>
      intro shapePrefix suffix _hnodup _hcondition
      simp [typedFieldsConformToShapeBool]
  | succ fuel ih =>
      intro shapePrefix suffix hnodup hcondition
      cases suffix with
      | nil =>
          simp [typedResponseFields, typedFieldsConformToShapeBool]
      | cons field rest =>
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
              typedVariantConformsToShapeBool variableValues fuel runtimeType
                (TypedExecution.completeValue schema store variableValues executionFuel
                  ((schema.fieldReturnType? parentType field.fieldName).getD field.fieldName)
                  [] (store.resolveValue field.fieldName field.arguments source))
                [toShapeVariant condition field] = true := by
            cases fuel with
            | zero =>
                simp [typedVariantConformsToShapeBool]
            | succ shapeFuel =>
                exact typedResponseFieldConformsToShapeVariant schema store variableValues
                  shapeFuel executionFuel parentType runtimeType source condition field
                  hcondition
          have hrestNodup : responseNamesNodup ((shapePrefix ++ [field]) ++ rest) := by
            simpa [responseNamesNodup, responseNames, List.map_append,
              List.append_assoc] using hnodup
          have hrest :
              typedFieldsConformToShapeBool variableValues fuel runtimeType
                (typedResponseFields schema store variableValues executionFuel parentType
                  source rest)
                ⟨toShapeFields condition ((shapePrefix ++ [field]) ++ rest)⟩ = true :=
            ih (shapePrefix ++ [field]) rest hrestNodup hcondition
          have hrest' :
              typedFieldsConformToShapeBool variableValues fuel runtimeType
                (typedResponseFields schema store variableValues executionFuel parentType
                  source rest)
                ⟨toShapeFields condition (shapePrefix ++ field :: rest)⟩ = true := by
            simpa [List.append_assoc] using hrest
          have hrest'' :
              typedFieldsConformToShapeBool variableValues fuel runtimeType
                (List.map
                  (typedResponseField schema store variableValues executionFuel parentType
                    source)
                  rest)
                ⟨toShapeFields condition (shapePrefix ++ field :: rest)⟩ = true := by
            simpa [typedResponseFields] using hrest'
          simp [typedResponseFields, typedResponseField, typedFieldsConformToShapeBool,
            hlookup, hvariant, hrest'']

theorem typedFieldsConformToShapeFieldsWithFuel
    (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues) (shapeFuel executionFuel : Nat)
    (parentType runtimeType : Name) (source : Value)
    (condition : ResponseShape.Condition) (fields : List LeafField) :
    responseNamesNodup fields ->
      conditionHoldsBool variableValues runtimeType condition = true ->
        typedFieldsConformToShapeBool variableValues shapeFuel runtimeType
          (typedResponseFields schema store variableValues executionFuel parentType
            source fields)
          ⟨toShapeFields condition fields⟩ = true := by
  intro hnodup hcondition
  simpa using
    typedFieldsConformToShapeFieldsWithFuel_append schema store variableValues
      executionFuel parentType runtimeType source condition shapeFuel [] fields hnodup
      hcondition

theorem typedResponseConformsToShape_completeValue_objectSelectionSetWithFuel
    (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues) (shapeFuel executionFuel : Nat)
    (declaredParentType runtimeType : Name) (id : ObjectId)
    (condition : ResponseShape.Condition) (fields : List LeafField) :
    responseNamesNodup fields ->
      conditionHoldsBool variableValues runtimeType condition = true ->
        typedResponseConformsToShapeBool variableValues (shapeFuel + 1)
          (TypedExecution.completeValue schema store variableValues (executionFuel + 2)
            declaredParentType (toSelectionSet fields) (.object runtimeType id))
          ⟨toShapeFields condition fields⟩ = true := by
  intro hnodup hcondition
  have hexec :
      TypedExecution.executeSelectionSet schema store variableValues (executionFuel + 1)
        runtimeType (.object runtimeType id) (toSelectionSet fields)
      =
        typedResponseFields schema store variableValues executionFuel runtimeType
          (.object runtimeType id) fields :=
    executeSelectionSet_toSelectionSet schema store variableValues executionFuel
      runtimeType (.object runtimeType id) fields hnodup
  have hfields :
      typedFieldsConformToShapeBool variableValues shapeFuel runtimeType
        (typedResponseFields schema store variableValues executionFuel runtimeType
          (.object runtimeType id) fields)
        ⟨toShapeFields condition fields⟩ = true :=
    typedFieldsConformToShapeFieldsWithFuel schema store variableValues shapeFuel
      executionFuel runtimeType runtimeType (.object runtimeType id) condition fields
      hnodup hcondition
  simpa [TypedExecution.completeValue, typedResponseConformsToShapeBool, hexec]
    using hfields

theorem typedResponseConformsToShape_completeValue_objectSelectionSet
    (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues) (executionFuel : Nat)
    (declaredParentType runtimeType : Name) (id : ObjectId)
    (condition : ResponseShape.Condition) (fields : List LeafField) :
    responseNamesNodup fields ->
      conditionHoldsBool variableValues runtimeType condition = true ->
        typedResponseConformsToShapeBool variableValues (fields.length + 1)
          (TypedExecution.completeValue schema store variableValues (executionFuel + 2)
            declaredParentType (toSelectionSet fields) (.object runtimeType id))
          ⟨toShapeFields condition fields⟩ = true := by
  exact typedResponseConformsToShape_completeValue_objectSelectionSetWithFuel
    schema store variableValues fields.length executionFuel declaredParentType
    runtimeType id condition fields

theorem typedVariantConformsToShape_parentObjectSelectionSetWithFuel
    (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues) (shapeFuel executionFuel : Nat)
    (parentRuntimeType declaredParentType runtimeType : Name) (id : ObjectId)
    (parentHeader : ResponseShape.VariantHeader)
    (childCondition : ResponseShape.Condition) (fields : List LeafField) :
    responseNamesNodup fields ->
      variantHeaderActiveBool variableValues parentRuntimeType parentHeader = true ->
      conditionHoldsBool variableValues runtimeType childCondition = true ->
        typedVariantConformsToShapeBool variableValues (shapeFuel + 2) parentRuntimeType
          (TypedExecution.completeValue schema store variableValues (executionFuel + 2)
            declaredParentType (toSelectionSet fields) (.object runtimeType id))
          [(parentHeader, ⟨toShapeFields childCondition fields⟩)] = true := by
  intro hnodup hparentActive hchildCondition
  have hchild :
      typedResponseConformsToShapeBool variableValues (shapeFuel + 1)
        (TypedExecution.completeValue schema store variableValues (executionFuel + 2)
          declaredParentType (toSelectionSet fields) (.object runtimeType id))
        ⟨toShapeFields childCondition fields⟩ = true :=
    typedResponseConformsToShape_completeValue_objectSelectionSetWithFuel schema store
      variableValues shapeFuel executionFuel declaredParentType runtimeType id
      childCondition fields hnodup hchildCondition
  exact typedVariantConformsToShapeBool_singleton variableValues (shapeFuel + 1)
    parentRuntimeType
    (TypedExecution.completeValue schema store variableValues (executionFuel + 2)
      declaredParentType (toSelectionSet fields) (.object runtimeType id))
    parentHeader ⟨toShapeFields childCondition fields⟩ hparentActive hchild

theorem typedResponseConformsToShape_completeValue_objectSelectionSetAnyFuel
    (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues) (responseFuel executionFuel : Nat)
    (declaredParentType runtimeType : Name) (id : ObjectId)
    (condition : ResponseShape.Condition) (fields : List LeafField) :
    responseNamesNodup fields ->
      conditionHoldsBool variableValues runtimeType condition = true ->
        typedResponseConformsToShapeBool variableValues responseFuel
          (TypedExecution.completeValue schema store variableValues (executionFuel + 2)
            declaredParentType (toSelectionSet fields) (.object runtimeType id))
          ⟨toShapeFields condition fields⟩ = true := by
  intro hnodup hcondition
  cases responseFuel with
  | zero =>
      simp [typedResponseConformsToShapeBool]
  | succ shapeFuel =>
      exact typedResponseConformsToShape_completeValue_objectSelectionSetWithFuel
        schema store variableValues shapeFuel executionFuel declaredParentType
        runtimeType id condition fields hnodup hcondition

theorem typedVariantConformsToShape_parentObjectSelectionSetAnyFuel
    (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues) (responseFuel executionFuel : Nat)
    (parentRuntimeType declaredParentType runtimeType : Name) (id : ObjectId)
    (parentHeader : ResponseShape.VariantHeader)
    (childCondition : ResponseShape.Condition) (fields : List LeafField) :
    responseNamesNodup fields ->
      variantHeaderActiveBool variableValues parentRuntimeType parentHeader = true ->
      conditionHoldsBool variableValues runtimeType childCondition = true ->
        typedVariantConformsToShapeBool variableValues (responseFuel + 1)
          parentRuntimeType
          (TypedExecution.completeValue schema store variableValues (executionFuel + 2)
            declaredParentType (toSelectionSet fields) (.object runtimeType id))
          [(parentHeader, ⟨toShapeFields childCondition fields⟩)] = true := by
  intro hnodup hparentActive hchildCondition
  have hchild :
      typedResponseConformsToShapeBool variableValues responseFuel
        (TypedExecution.completeValue schema store variableValues (executionFuel + 2)
          declaredParentType (toSelectionSet fields) (.object runtimeType id))
        ⟨toShapeFields childCondition fields⟩ = true :=
    typedResponseConformsToShape_completeValue_objectSelectionSetAnyFuel schema store
      variableValues responseFuel executionFuel declaredParentType runtimeType id
      childCondition fields hnodup hchildCondition
  exact typedVariantConformsToShapeBool_singleton variableValues responseFuel
    parentRuntimeType
    (TypedExecution.completeValue schema store variableValues (executionFuel + 2)
      declaredParentType (toSelectionSet fields) (.object runtimeType id))
    parentHeader ⟨toShapeFields childCondition fields⟩ hparentActive hchild

theorem typedResponseConformsToShape_completeValue_namedCompositeSelectionSetAnyFuel
    (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues) (responseFuel executionFuel : Nat)
    (parentType childType : Name) (fields : List LeafField) (value : Value) :
    responseNamesNodup fields ->
      Value.conformsToType schema value (.named childType) ->
      ¬ schema.getPossibleTypes childType = [] ->
        typedResponseConformsToShapeBool variableValues responseFuel
          (TypedExecution.completeValue schema store variableValues (executionFuel + 2)
            parentType (toSelectionSet fields) value)
          ⟨toShapeFields
            { possibleTypes := some (schema.getPossibleTypes childType),
              booleanLiterals := [] }
            fields⟩ = true := by
  intro hnodup hconforms hchildNonempty
  cases value with
  | null =>
      cases responseFuel <;>
        simp [TypedExecution.completeValue, typedResponseConformsToShapeBool]
  | scalar scalarValue =>
      exact False.elim
        ((scalar_not_conformsToType_of_possibleTypes_nonempty schema scalarValue
          (.named childType) (by simpa [TypeRef.namedType] using hchildNonempty))
          hconforms)
  | object runtimeType id =>
      have hchildType : schema.typeIncludesObject childType runtimeType :=
        object_conformsToType_typeIncludesObject schema runtimeType id childType
          (.named childType) (by simp [TypeRef.namedType]) hconforms
      have hcondition :
          conditionHoldsBool variableValues runtimeType
            { possibleTypes := some (schema.getPossibleTypes childType),
              booleanLiterals := [] } = true := by
        simp [conditionHoldsBool,
          possibleTypesHoldBool_of_typeIncludesObject schema hchildType]
      exact
        typedResponseConformsToShape_completeValue_objectSelectionSetAnyFuel
          schema store variableValues responseFuel executionFuel parentType runtimeType id
          { possibleTypes := some (schema.getPossibleTypes childType),
            booleanLiterals := [] }
          fields hnodup hcondition
  | list values =>
      cases hconforms

theorem typedResponseConformsToShape_completeValue_namedCompositeListSelectionSetAnyFuel
    (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues) (responseFuel executionFuel : Nat)
    (parentType childType : Name) (fields : List LeafField) (values : List Value) :
    responseNamesNodup fields ->
      (∀ value, value ∈ values -> Value.conformsToType schema value (.named childType)) ->
      ¬ schema.getPossibleTypes childType = [] ->
        (values.map
          (TypedExecution.completeValue schema store variableValues (executionFuel + 2)
            parentType (toSelectionSet fields))).all
          (fun response =>
            typedResponseConformsToShapeBool variableValues responseFuel response
              ⟨toShapeFields
                { possibleTypes := some (schema.getPossibleTypes childType),
                  booleanLiterals := [] }
                fields⟩) = true := by
  intro hnodup hconforms hchildNonempty
  induction values with
  | nil =>
      simp
  | cons value rest ih =>
      have hvalue :
          typedResponseConformsToShapeBool variableValues responseFuel
            (TypedExecution.completeValue schema store variableValues (executionFuel + 2)
              parentType (toSelectionSet fields) value)
            ⟨toShapeFields
              { possibleTypes := some (schema.getPossibleTypes childType),
                booleanLiterals := [] }
              fields⟩ = true :=
        typedResponseConformsToShape_completeValue_namedCompositeSelectionSetAnyFuel
          schema store variableValues responseFuel executionFuel parentType childType
          fields value hnodup (hconforms value (by simp)) hchildNonempty
      have hrestConforms :
          ∀ value, value ∈ rest ->
            Value.conformsToType schema value (.named childType) := by
        intro restValue hmem
        exact hconforms restValue (by simp [hmem])
      have hrest := ih hrestConforms
      simp [hvalue, hrest]

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

theorem groundNormalFormCorrect_twoSameCompositeLeafFieldsNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName : Name) (parentArguments : List Argument)
    (leftFields rightFields : List LeafField) :
    LeafField.responseNamesNodup (leftFields ++ rightFields) ->
      groundNormalFormCorrect schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [
            .field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet leftFields),
            .field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet rightFields)
          ] } := by
  intro hnodup
  rw [groundNormalFormCorrect]
  rw [LeafField.normalizeSemanticOperation_twoSameCompositeLeafFieldsNoDirectives
    schema name rootType variableDefinitions parentResponseName parentFieldName
    parentArguments leftFields rightFields hnodup]
  intro store variableValues root _hstore _hroot
  simp [executeSemanticQueryWithFuel, Execution.executeSemanticQueryFuel,
    Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
    LeafField.toSelectionSet_size, LeafField.toSelectionSet_append,
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

set_option linter.unusedSimpArgs false in
theorem normalFormPreservesResponseShapeBool_twoSameCompositeDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName : Name) (parentArguments : List Argument)
    (leftResponseName leftFieldName : Name) (leftArguments : List Argument)
    (rightResponseName rightFieldName : Name) (rightArguments : List Argument) :
    leftResponseName ≠ rightResponseName ->
      normalFormPreservesResponseShapeBool schema
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
          ] } = true := by
  intro hdistinct
  have hdistinct' : rightResponseName ≠ leftResponseName := Ne.symm hdistinct
  let childType := (schema.fieldReturnType? rootType parentFieldName).getD parentFieldName
  rw [normalFormPreservesResponseShapeBool]
  rw [NormalForm.normalizeSemanticOperation_twoSameCompositeDistinctLeafNoDirectives
    schema name rootType variableDefinitions parentResponseName parentFieldName
    parentArguments leftResponseName leftFieldName leftArguments rightResponseName
    rightFieldName rightArguments hdistinct]
  by_cases hrootEmpty : schema.getPossibleTypes rootType = []
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
      hrootEmpty, ResponseShape.Shape.equivalentBool, ResponseShape.Shape.includesBool,
      ResponseShape.Shape.includesFieldsBool]
  · by_cases hchildEmpty : schema.getPossibleTypes childType = []
    · simp [childType, ResponseShape.Shape.ofSemanticOperation,
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
        ResponseShape.Condition.forChildType, hrootEmpty, hchildEmpty,
        ResponseShape.Shape.mergeFields, ResponseShape.Shape.merge,
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
    · simp [childType, ResponseShape.Shape.ofSemanticOperation,
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
        ResponseShape.Condition.forChildType, hrootEmpty, hchildEmpty, hdistinct, hdistinct',
        LeafField.mergeFields_parentVariant_twoChildShapeFields,
        ResponseShape.Shape.mergeFields, ResponseShape.Shape.merge,
        ResponseShape.Shape.size, ResponseShape.Shape.fieldsSize,
        ResponseShape.Shape.variantsSize, ResponseShape.Shape.mergeWithFuel,
        ResponseShape.Shape.mergeFieldsWithFuel, ResponseShape.Shape.mergeVariantsWithFuel,
        ResponseShape.Shape.equivalentBool, ResponseShape.Shape.includesBool,
        ResponseShape.Shape.includesFieldsBool, ResponseShape.Shape.includesVariantsBool,
        ResponseShape.Shape.lookupField, ResponseShape.Shape.lookupIncludingVariant,
        ResponseShape.VariantHeader.eqBool_self,
        ResponseShape.VariantHeader.includedByBool_self,
        ResponseShape.Shape.empty_includesBool]

theorem normalFormPreservesResponseShape_twoSameCompositeDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName : Name) (parentArguments : List Argument)
    (leftResponseName leftFieldName : Name) (leftArguments : List Argument)
    (rightResponseName rightFieldName : Name) (rightArguments : List Argument) :
    leftResponseName ≠ rightResponseName ->
      normalFormPreservesResponseShape schema
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
  exact normalFormPreservesResponseShapeBool_sound schema _
    (normalFormPreservesResponseShapeBool_twoSameCompositeDistinctLeafNoDirectives schema name
      rootType variableDefinitions parentResponseName parentFieldName parentArguments
      leftResponseName leftFieldName leftArguments rightResponseName rightFieldName
      rightArguments hdistinct)

set_option linter.unusedSimpArgs false in
theorem normalFormPreservesResponseShapeBool_twoSameCompositeLeafFieldsNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName : Name) (parentArguments : List Argument)
    (leftFields rightFields : List LeafField) :
    LeafField.responseNamesNodup (leftFields ++ rightFields) ->
      normalFormPreservesResponseShapeBool schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [
            .field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet leftFields),
            .field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet rightFields)
          ] } = true := by
  intro hnodup
  let rootCondition : ResponseShape.Condition :=
    { possibleTypes := some (schema.getPossibleTypes rootType), booleanLiterals := [] }
  let childType := (schema.fieldReturnType? rootType parentFieldName).getD parentFieldName
  let childCondition := ResponseShape.Condition.forChildType schema rootCondition childType
  let parentHeader : ResponseShape.VariantHeader :=
    (rootCondition, ResponseShape.selectedField parentFieldName parentArguments)
  have hsourceInitial :
      ResponseShape.Shape.semanticOperationInitialCondition schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [
            .field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet leftFields),
            .field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet rightFields)
          ] } = rootCondition := by
    rfl
  have hnormalizedInitial :
      ResponseShape.Shape.semanticOperationInitialCondition schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [
            .field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet (leftFields ++ rightFields))
          ] } = rootCondition := by
    rfl
  have hnormalizedInitialAppend :
      ResponseShape.Shape.semanticOperationInitialCondition schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [
            .field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
          ] } = rootCondition := by
    rfl
  have hselectionSetSizeAppend :
      Semantic.SelectionSet.size
        (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
        = leftFields.length + rightFields.length := by
    rw [← LeafField.toSelectionSet_append, LeafField.toSelectionSet_size]
    simp [List.length_append]
  rw [normalFormPreservesResponseShapeBool]
  rw [LeafField.normalizeSemanticOperation_twoSameCompositeLeafFieldsNoDirectives
    schema name rootType variableDefinitions parentResponseName parentFieldName
    parentArguments leftFields rightFields hnodup]
  by_cases hrootEmpty : schema.getPossibleTypes rootType = []
  · simp [rootCondition, childType, childCondition, parentHeader,
      ResponseShape.Shape.ofSemanticOperation,
      ResponseShape.Shape.semanticOperationShapeFuel,
      Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
      LeafField.toSelectionSet_size, LeafField.toSelectionSet_append,
      ResponseShape.Shape.semanticSelectionSetShape,
      ResponseShape.Shape.collectSelectionSetShapeFields,
      ResponseShape.Shape.collectSelectionShapeFields,
      ResponseShape.Condition.fromDirectives?, ResponseShape.Condition.empty,
      ResponseShape.Shape.empty, ResponseShape.Condition.satisfiableBool,
      ResponseShape.Condition.hasContradictionBool,
      ResponseShape.BooleanLiteral.hasContradictionBool,
      ResponseShape.Condition.possibleTypesEmptyBool,
      ResponseShape.Condition.and, ResponseShape.Shape.semanticOperationInitialCondition,
      hrootEmpty, ResponseShape.Shape.equivalentBool, ResponseShape.Shape.includesBool,
      ResponseShape.Shape.includesFieldsBool]
  · have hrootSat : rootCondition.satisfiableBool = true := by
      simp [rootCondition, ResponseShape.Condition.satisfiableBool,
        ResponseShape.Condition.hasContradictionBool,
        ResponseShape.BooleanLiteral.hasContradictionBool,
        ResponseShape.Condition.possibleTypesEmptyBool, hrootEmpty]
    by_cases hchildEmpty : schema.getPossibleTypes childType = []
    · have hchildUnsat : childCondition.satisfiableBool = false := by
        simp [childCondition, rootCondition, childType,
          ResponseShape.Condition.satisfiableBool,
          ResponseShape.Condition.hasContradictionBool,
          ResponseShape.BooleanLiteral.hasContradictionBool,
          ResponseShape.Condition.possibleTypesEmptyBool, hchildEmpty]
      have hleftField :
          ResponseShape.Shape.collectSelectionShapeFields schema
            (leftFields.length + rightFields.length + 2 + 1) rootType rootCondition
            (.field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet leftFields))
          =
            [(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ResponseShape.Shape.empty)])] := by
        simpa [childType, childCondition, rootCondition] using
          LeafField.collectSelectionShapeFields_field_toSelectionSet_unsat
            schema (leftFields.length + rightFields.length + 2) rootType
            rootCondition parentResponseName parentFieldName parentArguments
            leftFields hrootSat hchildUnsat
      have hrightField :
          ResponseShape.Shape.collectSelectionShapeFields schema
            (leftFields.length + rightFields.length + 2 + 1) rootType rootCondition
            (.field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet rightFields))
          =
            [(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ResponseShape.Shape.empty)])] := by
        simpa [childType, childCondition, rootCondition] using
          LeafField.collectSelectionShapeFields_field_toSelectionSet_unsat
            schema (leftFields.length + rightFields.length + 2) rootType
            rootCondition parentResponseName parentFieldName parentArguments
            rightFields hrootSat hchildUnsat
      have hcombinedField :
          ResponseShape.Shape.collectSelectionShapeFields schema
            (leftFields.length + rightFields.length + 1 + 1) rootType rootCondition
            (.field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet (leftFields ++ rightFields)))
          =
            [(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ResponseShape.Shape.empty)])] := by
        simpa [childType, childCondition, rootCondition] using
          LeafField.collectSelectionShapeFields_field_toSelectionSet_unsat
            schema (leftFields.length + rightFields.length + 1) rootType
            rootCondition parentResponseName parentFieldName parentArguments
            (leftFields ++ rightFields) hrootSat hchildUnsat
      have hleftFieldNorm :
          ResponseShape.Shape.collectSelectionShapeFields schema
            (leftFields.length + (rightFields.length + 3)) rootType rootCondition
            (.field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet leftFields))
          =
            [(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ResponseShape.Shape.empty)])] := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hleftField
      have hrightFieldNorm :
          ResponseShape.Shape.collectSelectionShapeFields schema
            (leftFields.length + (rightFields.length + 3)) rootType rootCondition
            (.field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet rightFields))
          =
            [(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ResponseShape.Shape.empty)])] := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrightField
      have hcombinedFieldNorm :
          ResponseShape.Shape.collectSelectionShapeFields schema
            (leftFields.length + (rightFields.length + 2)) rootType rootCondition
            (.field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields))
          =
            [(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ResponseShape.Shape.empty)])] := by
        simpa [LeafField.toSelectionSet_append, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hcombinedField
      have hfieldNil :
          ResponseShape.Shape.mergeFields
            [(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ResponseShape.Shape.empty)])]
            []
            =
              [(parentResponseName,
                [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                  ResponseShape.Shape.empty)])] :=
        LeafField.mergeFields_parentVariant_childShape_nil
          parentResponseName
          (rootCondition, ResponseShape.selectedField parentFieldName parentArguments)
          ResponseShape.Shape.empty
      have hequivEmpty :
          ResponseShape.Shape.equivalentBool
            ⟨[(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ResponseShape.Shape.empty)])]⟩
            ⟨[(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ResponseShape.Shape.empty)])]⟩ = true :=
        ResponseShape.Shape.equivalentBool_singleton_empty_self parentResponseName
          (rootCondition, ResponseShape.selectedField parentFieldName parentArguments)
      simp [ResponseShape.Shape.ofSemanticOperation,
        ResponseShape.Shape.semanticOperationShapeFuel,
        Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
        LeafField.toSelectionSet_size,
        ResponseShape.Shape.semanticSelectionSetShape,
        ResponseShape.Shape.collectSelectionSetShapeFields, hrootSat,
        hsourceInitial, hnormalizedInitial, hnormalizedInitialAppend,
        hselectionSetSizeAppend, hleftFieldNorm, hrightFieldNorm,
        hcombinedFieldNorm, hfieldNil, hequivEmpty,
        ResponseShape.Shape.mergeFields_singleton_empty_self,
        ResponseShape.Shape.equivalentBool, ResponseShape.Shape.includesBool,
        ResponseShape.Shape.includesFieldsBool, ResponseShape.Shape.includesVariantsBool,
        ResponseShape.Shape.lookupField, ResponseShape.Shape.lookupIncludingVariant,
        ResponseShape.VariantHeader.includedByBool_self,
        ResponseShape.Shape.empty_includesBool,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · have hchildSat : childCondition.satisfiableBool = true := by
        simp [childCondition, rootCondition, childType,
          ResponseShape.Condition.satisfiableBool,
          ResponseShape.Condition.hasContradictionBool,
          ResponseShape.BooleanLiteral.hasContradictionBool,
          ResponseShape.Condition.possibleTypesEmptyBool, hchildEmpty]
      have hnameParts :
          (LeafField.responseNames leftFields ++ LeafField.responseNames rightFields).Nodup := by
        simpa [LeafField.responseNamesNodup, LeafField.responseNames, List.map_append]
          using hnodup
      have hleftNodup : LeafField.responseNamesNodup leftFields := by
        have hparts := hnameParts
        simp [List.nodup_append] at hparts
        exact hparts.left
      have hrightNodup : LeafField.responseNamesNodup rightFields := by
        have hparts := hnameParts
        simp [List.nodup_append] at hparts
        exact hparts.right.left
      have hleftField :
          ResponseShape.Shape.collectSelectionShapeFields schema
            (leftFields.length + rightFields.length + 2 + 1) rootType rootCondition
            (.field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet leftFields))
          =
            [(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ⟨LeafField.toShapeFields childCondition leftFields⟩)])] := by
        simpa [childType, childCondition, rootCondition] using
          LeafField.collectSelectionShapeFields_field_toSelectionSet
            schema (leftFields.length + rightFields.length + 2) rootType
            rootCondition parentResponseName parentFieldName parentArguments
            leftFields hrootSat hchildSat (by omega) hleftNodup
      have hrightField :
          ResponseShape.Shape.collectSelectionShapeFields schema
            (leftFields.length + rightFields.length + 2 + 1) rootType rootCondition
            (.field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet rightFields))
          =
            [(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ⟨LeafField.toShapeFields childCondition rightFields⟩)])] := by
        simpa [childType, childCondition, rootCondition] using
          LeafField.collectSelectionShapeFields_field_toSelectionSet
            schema (leftFields.length + rightFields.length + 2) rootType
            rootCondition parentResponseName parentFieldName parentArguments
            rightFields hrootSat hchildSat (by omega) hrightNodup
      have hcombinedField :
          ResponseShape.Shape.collectSelectionShapeFields schema
            (leftFields.length + rightFields.length + 1 + 1) rootType rootCondition
            (.field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet (leftFields ++ rightFields)))
          =
            [(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ⟨LeafField.toShapeFields childCondition (leftFields ++ rightFields)⟩)])] := by
        simpa [childType, childCondition, rootCondition] using
          LeafField.collectSelectionShapeFields_field_toSelectionSet
            schema (leftFields.length + rightFields.length + 1) rootType
            rootCondition parentResponseName parentFieldName parentArguments
            (leftFields ++ rightFields) hrootSat hchildSat (by simp) hnodup
      have hleftFieldNorm :
          ResponseShape.Shape.collectSelectionShapeFields schema
            (leftFields.length + (rightFields.length + 3)) rootType rootCondition
            (.field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet leftFields))
          =
            [(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ⟨LeafField.toShapeFields childCondition leftFields⟩)])] := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hleftField
      have hrightFieldNorm :
          ResponseShape.Shape.collectSelectionShapeFields schema
            (leftFields.length + (rightFields.length + 3)) rootType rootCondition
            (.field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet rightFields))
          =
            [(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ⟨LeafField.toShapeFields childCondition rightFields⟩)])] := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrightField
      have hcombinedFieldNorm :
          ResponseShape.Shape.collectSelectionShapeFields schema
            (leftFields.length + (rightFields.length + 2)) rootType rootCondition
            (.field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields))
          =
            [(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ⟨LeafField.toShapeFields childCondition (leftFields ++ rightFields)⟩)])] := by
        simpa [LeafField.toSelectionSet_append, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hcombinedField
      have hrightNil :
          ResponseShape.Shape.mergeFields
            [(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ⟨LeafField.toShapeFields childCondition rightFields⟩)])]
            []
            =
              [(parentResponseName,
                [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                  ⟨LeafField.toShapeFields childCondition rightFields⟩)])] :=
        LeafField.mergeFields_parentVariant_childShape_nil
          parentResponseName
          (rootCondition, ResponseShape.selectedField parentFieldName parentArguments)
          ⟨LeafField.toShapeFields childCondition rightFields⟩
      have hcombinedNil :
          ResponseShape.Shape.mergeFields
            [(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ⟨LeafField.toShapeFields childCondition (leftFields ++ rightFields)⟩)])]
            []
            =
              [(parentResponseName,
                [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                  ⟨LeafField.toShapeFields childCondition (leftFields ++ rightFields)⟩)])] :=
        LeafField.mergeFields_parentVariant_childShape_nil
          parentResponseName
          (rootCondition, ResponseShape.selectedField parentFieldName parentArguments)
          ⟨LeafField.toShapeFields childCondition (leftFields ++ rightFields)⟩
      have hmerge :
          ResponseShape.Shape.mergeFields
            [(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ⟨LeafField.toShapeFields childCondition leftFields⟩)])]
            [(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ⟨LeafField.toShapeFields childCondition rightFields⟩)])]
            =
              [(parentResponseName,
                [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                  ⟨LeafField.toShapeFields childCondition
                    (leftFields ++ rightFields)⟩)])] :=
        LeafField.mergeFields_parentVariant_childShapeFields_append
          parentResponseName
          (rootCondition, ResponseShape.selectedField parentFieldName parentArguments)
          childCondition leftFields rightFields hnodup
      have hequiv :
          ResponseShape.Shape.equivalentBool
            ⟨[(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ⟨LeafField.toShapeFields childCondition
                  (leftFields ++ rightFields)⟩)])]⟩
            ⟨[(parentResponseName,
              [((rootCondition, ResponseShape.selectedField parentFieldName parentArguments),
                ⟨LeafField.toShapeFields childCondition
                  (leftFields ++ rightFields)⟩)])]⟩ = true :=
        LeafField.equivalentBool_parentVariant_childShapeFields_self
          parentResponseName
          (rootCondition, ResponseShape.selectedField parentFieldName parentArguments)
          childCondition (leftFields ++ rightFields) hnodup
      simp [ResponseShape.Shape.ofSemanticOperation,
        ResponseShape.Shape.semanticOperationShapeFuel,
        Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
        LeafField.toSelectionSet_size,
        ResponseShape.Shape.semanticSelectionSetShape,
        ResponseShape.Shape.collectSelectionSetShapeFields, hrootSat,
        hsourceInitial, hnormalizedInitial, hnormalizedInitialAppend,
        hselectionSetSizeAppend, hleftFieldNorm, hrightFieldNorm,
        hcombinedFieldNorm, hrightNil, hcombinedNil,
        hmerge, hequiv,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem normalFormPreservesResponseShape_twoSameCompositeLeafFieldsNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName : Name) (parentArguments : List Argument)
    (leftFields rightFields : List LeafField) :
    LeafField.responseNamesNodup (leftFields ++ rightFields) ->
      normalFormPreservesResponseShape schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [
            .field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet leftFields),
            .field parentResponseName parentFieldName parentArguments []
              (LeafField.toSelectionSet rightFields)
          ] } := by
  intro hnodup
  exact normalFormPreservesResponseShapeBool_sound schema _
    (normalFormPreservesResponseShapeBool_twoSameCompositeLeafFieldsNoDirectives schema name
      rootType variableDefinitions parentResponseName parentFieldName parentArguments
      leftFields rightFields hnodup)

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
theorem responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeDistinctLeafNoDirectives_ofObjectOutput
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName childType : Name)
    (parentArguments : List Argument)
    (leftResponseName leftFieldName : Name) (leftArguments : List Argument)
    (rightResponseName rightFieldName : Name) (rightArguments : List Argument)
    (rootObject : ObjectType) (parentFieldDefinition : FieldDefinition) :
    schema.lookupType rootType = some (.object rootObject) ->
      schema.lookupField rootType parentFieldName = some parentFieldDefinition ->
      parentFieldDefinition.outputType.namedType = childType ->
      (∀ values, ¬ Value.conformsToType schema (.list values) parentFieldDefinition.outputType) ->
      ¬ schema.getPossibleTypes childType = [] ->
      leftResponseName ≠ rightResponseName ->
        responseShapeCorrectForTypedExecutionAtRoot schema
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
  intro hrootObject hparentField hparentNamed hlistImpossible hchildNonempty hdistinct store
    variableValues root hstore _hroot hrootType
  have hdistinct' : rightResponseName ≠ leftResponseName := Ne.symm hdistinct
  have hrootEq : root.typeName = rootType :=
    typeIncludesObject_eq_of_lookupObjectType schema hrootObject hrootType
  have hrootPossibleNonempty : ¬ schema.getPossibleTypes rootType = [] :=
    possibleTypes_nonempty_of_typeIncludesObject schema hrootType
  have hparentFieldRoot :
      schema.lookupField root.typeName parentFieldName = some parentFieldDefinition := by
    simpa [hrootEq] using hparentField
  have hnotScalar :
      ∀ value,
        store.resolveValue parentFieldName parentArguments
            (Value.object root.typeName root.id) ≠ .scalar value := by
    intro value
    exact Store.resolveValue_ne_scalar_of_compositeLookupField schema store root.typeName
      root.id parentFieldName parentArguments parentFieldDefinition value hstore
      hparentFieldRoot (by simpa [hparentNamed] using hchildNonempty)
  have hresolvedConforms :
      store.resolveValue parentFieldName parentArguments
          (Value.object root.typeName root.id) = .null
        ∨ Value.conformsToType schema
          (store.resolveValue parentFieldName parentArguments
            (Value.object root.typeName root.id))
          parentFieldDefinition.outputType :=
    Store.resolveValue_conformsToLookupField schema store root.typeName root.id
      parentFieldName parentArguments parentFieldDefinition hstore hparentFieldRoot
  cases hresolved :
      store.resolveValue parentFieldName parentArguments
        (Value.object root.typeName root.id) with
  | null =>
      simp [TypedExecution.executeSemanticQuery, Execution.executeSemanticQueryFuel,
        Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
        TypedExecution.executeSelectionSet, Execution.collectFields,
        Execution.collectSelection, Execution.selectionDirectivesAllowBool,
        Execution.mergeExecutableGroups, Execution.addExecutableGroup,
        Execution.addExecutableFields, Execution.addExecutableField,
        Execution.mergedFieldSelectionSet, TypedExecution.executeCollectedFields,
        TypedExecution.executeField, TypedExecution.completeValue, hresolved,
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
        ResponseShape.Condition.and, ResponseShape.Condition.forChildType,
        ResponseShape.Shape.semanticOperationInitialCondition, hrootPossibleNonempty,
        hchildNonempty, hdistinct, hdistinct', hparentField, hparentNamed,
        Schema.fieldReturnType?, TypeRef.namedType,
        LeafField.mergeFields_parentVariant_twoChildShapeFields,
        ResponseShape.Shape.mergeFields,
        ResponseShape.Shape.merge, ResponseShape.Shape.size,
        ResponseShape.Shape.fieldsSize, ResponseShape.Shape.variantsSize,
        ResponseShape.Shape.mergeWithFuel, ResponseShape.Shape.mergeFieldsWithFuel,
        ResponseShape.Shape.mergeVariantsWithFuel,
        ResponseShape.VariantHeader.eqBool_self, typedResponseConformsToShapeBool,
        typedFieldsConformToShapeBool, typedVariantConformsToShapeBool,
        variantHeaderActiveBool, conditionHoldsBool,
        possibleTypesHoldBool_of_typeIncludesObject schema hrootType,
        ResponseShape.Shape.lookupField]
  | scalar value =>
      exact False.elim (hnotScalar value hresolved)
  | object runtimeType id =>
      have hconforms :
          Value.conformsToType schema (.object runtimeType id)
            parentFieldDefinition.outputType := by
        cases hresolvedConforms with
        | inl hnull =>
            rw [hresolved] at hnull
            cases hnull
        | inr hconforms =>
            simpa [hresolved] using hconforms
      have hchildType : schema.typeIncludesObject childType runtimeType :=
        object_conformsToType_typeIncludesObject schema runtimeType id childType
          parentFieldDefinition.outputType hparentNamed hconforms
      have hchildCondition :
          conditionHoldsBool variableValues runtimeType
            (ResponseShape.Condition.forChildType schema
              { possibleTypes := some (schema.getPossibleTypes rootType),
                booleanLiterals := [] }
              childType) = true := by
        exact conditionHoldsBool_forChildType schema variableValues
          (condition :=
            { possibleTypes := some (schema.getPossibleTypes rootType),
              booleanLiterals := [] })
          (by simp) hchildType
      simp [TypedExecution.executeSemanticQuery, Execution.executeSemanticQueryFuel,
        Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
        TypedExecution.executeSelectionSet, Execution.collectFields,
        Execution.collectSelection, Execution.selectionDirectivesAllowBool,
        Execution.mergeExecutableGroups, Execution.addExecutableGroup,
        Execution.addExecutableFields, Execution.addExecutableField,
        Execution.mergedFieldSelectionSet, TypedExecution.executeCollectedFields,
        TypedExecution.executeField, TypedExecution.completeValue, hresolved,
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
        ResponseShape.Condition.and, ResponseShape.Condition.forChildType,
        ResponseShape.Shape.semanticOperationInitialCondition, hrootPossibleNonempty,
        hchildNonempty, hdistinct, hdistinct', hparentField, hparentNamed,
        Schema.fieldReturnType?, TypeRef.namedType,
        LeafField.mergeFields_parentVariant_twoChildShapeFields,
        ResponseShape.Shape.mergeFields,
        ResponseShape.Shape.merge, ResponseShape.Shape.size,
        ResponseShape.Shape.fieldsSize, ResponseShape.Shape.variantsSize,
        ResponseShape.Shape.mergeWithFuel, ResponseShape.Shape.mergeFieldsWithFuel,
        ResponseShape.Shape.mergeVariantsWithFuel,
        ResponseShape.VariantHeader.eqBool_self, typedResponseConformsToShapeBool,
        typedFieldsConformToShapeBool, typedVariantConformsToShapeBool,
        variantHeaderActiveBool, conditionHoldsBool,
        possibleTypesHoldBool_of_typeIncludesObject schema hrootType, hchildCondition,
        ResponseShape.Shape.lookupField]
  | list values =>
      cases hresolvedConforms with
      | inl hnull =>
          rw [hresolved] at hnull
          cases hnull
      | inr hconforms =>
          exact False.elim
            ((hlistImpossible values) (by simpa [hresolved] using hconforms))

set_option linter.unusedSimpArgs false in
theorem responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeLeafFieldsNoDirectives_ofObjectOutput
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName childType : Name)
    (parentArguments : List Argument)
    (leftFields rightFields : List LeafField)
    (rootObject : ObjectType) (parentFieldDefinition : FieldDefinition) :
    schema.lookupType rootType = some (.object rootObject) ->
      schema.lookupField rootType parentFieldName = some parentFieldDefinition ->
      parentFieldDefinition.outputType.namedType = childType ->
      (∀ values, ¬ Value.conformsToType schema (.list values) parentFieldDefinition.outputType) ->
      ¬ schema.getPossibleTypes childType = [] ->
      LeafField.responseNamesNodup (leftFields ++ rightFields) ->
        responseShapeCorrectForTypedExecutionAtRoot schema
          { name := name,
            rootType := rootType,
            variableDefinitions := variableDefinitions,
            selectionSet := [
              .field parentResponseName parentFieldName parentArguments []
                (LeafField.toSelectionSet leftFields),
              .field parentResponseName parentFieldName parentArguments []
                (LeafField.toSelectionSet rightFields)
            ] } := by
  intro hrootObject hparentField hparentNamed hlistImpossible hchildNonempty hchildNodup
    store variableValues root hstore _hroot hrootType
  have hrootEq : root.typeName = rootType :=
    typeIncludesObject_eq_of_lookupObjectType schema hrootObject hrootType
  have hrootPossibleNonempty : ¬ schema.getPossibleTypes rootType = [] :=
    possibleTypes_nonempty_of_typeIncludesObject schema hrootType
  have hparentFieldRoot :
      schema.lookupField root.typeName parentFieldName = some parentFieldDefinition := by
    simpa [hrootEq] using hparentField
  have hnotScalar :
      ∀ value,
        store.resolveValue parentFieldName parentArguments
            (Value.object root.typeName root.id) ≠ .scalar value := by
    intro value
    exact Store.resolveValue_ne_scalar_of_compositeLookupField schema store root.typeName
      root.id parentFieldName parentArguments parentFieldDefinition value hstore
      hparentFieldRoot (by simpa [hparentNamed] using hchildNonempty)
  have hresolvedConforms :
      store.resolveValue parentFieldName parentArguments
          (Value.object root.typeName root.id) = .null
        ∨ Value.conformsToType schema
          (store.resolveValue parentFieldName parentArguments
            (Value.object root.typeName root.id))
          parentFieldDefinition.outputType :=
    Store.resolveValue_conformsToLookupField schema store root.typeName root.id
      parentFieldName parentArguments parentFieldDefinition hstore hparentFieldRoot
  let childCondition : ResponseShape.Condition :=
    { possibleTypes := some (schema.getPossibleTypes childType), booleanLiterals := [] }
  have hchildConditionSat : childCondition.satisfiableBool = true := by
    simp [childCondition, ResponseShape.Condition.satisfiableBool,
      ResponseShape.Condition.hasContradictionBool,
      ResponseShape.Condition.possibleTypesEmptyBool,
      ResponseShape.BooleanLiteral.hasContradictionBool, hchildNonempty]
  have hnameParts :
      (LeafField.responseNames leftFields ++ LeafField.responseNames rightFields).Nodup := by
    simpa [LeafField.responseNamesNodup, LeafField.responseNames, List.map_append]
      using hchildNodup
  have hleftNodup : LeafField.responseNamesNodup leftFields := by
    have hparts := hnameParts
    simp [List.nodup_append] at hparts
    exact hparts.left
  have hrightNodup : LeafField.responseNamesNodup rightFields := by
    have hparts := hnameParts
    simp [List.nodup_append] at hparts
    exact hparts.right.left
  have hleftShape :
      (match LeafField.toSelectionSet leftFields with
      | [] => ResponseShape.Shape.empty
      | _ =>
          ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema
            (1 + leftFields.length + (1 + rightFields.length)) childType
            childCondition (LeafField.toSelectionSet leftFields)⟩)
        = ⟨LeafField.toShapeFields childCondition leftFields⟩ :=
    LeafField.childShape_toSelectionSet schema
      (1 + leftFields.length + (1 + rightFields.length)) childType childCondition
      leftFields (by omega) hchildConditionSat hleftNodup
  have hrightShape :
      (match LeafField.toSelectionSet rightFields with
      | [] => ResponseShape.Shape.empty
      | _ =>
          ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema
            (1 + leftFields.length + (1 + rightFields.length)) childType
            childCondition (LeafField.toSelectionSet rightFields)⟩)
        = ⟨LeafField.toShapeFields childCondition rightFields⟩ :=
    LeafField.childShape_toSelectionSet schema
      (1 + leftFields.length + (1 + rightFields.length)) childType childCondition
      rightFields (by omega) hchildConditionSat hrightNodup
  have hleftShapeRaw :
      (match LeafField.toSelectionSet leftFields with
      | [] => ResponseShape.Shape.empty
      | _ =>
          ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema
            (1 + leftFields.length + (1 + rightFields.length)) childType
            { possibleTypes := some (schema.getPossibleTypes childType),
              booleanLiterals := [] }
            (LeafField.toSelectionSet leftFields)⟩)
        =
          ⟨LeafField.toShapeFields
            { possibleTypes := some (schema.getPossibleTypes childType),
              booleanLiterals := [] }
            leftFields⟩ := by
    simpa [childCondition] using hleftShape
  have hrightShapeRaw :
      (match LeafField.toSelectionSet rightFields with
      | [] => ResponseShape.Shape.empty
      | _ =>
          ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema
            (1 + leftFields.length + (1 + rightFields.length)) childType
            { possibleTypes := some (schema.getPossibleTypes childType),
              booleanLiterals := [] }
            (LeafField.toSelectionSet rightFields)⟩)
        =
          ⟨LeafField.toShapeFields
            { possibleTypes := some (schema.getPossibleTypes childType),
              booleanLiterals := [] }
            rightFields⟩ := by
    simpa [childCondition] using hrightShape
  let parentHeader : ResponseShape.VariantHeader :=
    Prod.mk
      (ResponseShape.Condition.mk (some (schema.getPossibleTypes rootType)) [])
      (ResponseShape.selectedField parentFieldName parentArguments)
  let rawChildCondition : ResponseShape.Condition :=
    ResponseShape.Condition.mk (some (schema.getPossibleTypes childType)) []
  have hleftFieldShape :
      [(parentResponseName,
        [(parentHeader,
          match LeafField.toSelectionSet leftFields with
          | [] => ResponseShape.Shape.empty
          | _ =>
              ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema
                (1 + leftFields.length + (1 + rightFields.length)) childType
                rawChildCondition (LeafField.toSelectionSet leftFields)⟩)])]
        =
          [(parentResponseName,
            [(parentHeader,
              ⟨LeafField.toShapeFields rawChildCondition leftFields⟩)])] := by
    simpa [parentHeader, rawChildCondition] using
      congrArg
        (fun childShape : ResponseShape.Shape =>
          [(parentResponseName, [(parentHeader, childShape)])])
        hleftShapeRaw
  have hrightFieldShape :
      [(parentResponseName,
        [(parentHeader,
          match LeafField.toSelectionSet rightFields with
          | [] => ResponseShape.Shape.empty
          | _ =>
              ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema
                (1 + leftFields.length + (1 + rightFields.length)) childType
                rawChildCondition (LeafField.toSelectionSet rightFields)⟩)])]
        =
          [(parentResponseName,
            [(parentHeader,
              ⟨LeafField.toShapeFields rawChildCondition rightFields⟩)])] := by
    simpa [parentHeader, rawChildCondition] using
      congrArg
        (fun childShape : ResponseShape.Shape =>
          [(parentResponseName, [(parentHeader, childShape)])])
        hrightShapeRaw
  let mergedRawShape : ResponseShape.Shape :=
    { fields :=
      ResponseShape.Shape.mergeFields
        [(parentResponseName,
          [(parentHeader,
            match LeafField.toSelectionSet leftFields with
            | [] => ResponseShape.Shape.empty
            | _ =>
                ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema
                  (1 + leftFields.length + (1 + rightFields.length)) childType
                  rawChildCondition (LeafField.toSelectionSet leftFields)⟩)])]
        (ResponseShape.Shape.mergeFields
          [(parentResponseName,
            [(parentHeader,
              match LeafField.toSelectionSet rightFields with
              | [] => ResponseShape.Shape.empty
              | _ =>
                  ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema
                    (1 + leftFields.length + (1 + rightFields.length)) childType
                    rawChildCondition (LeafField.toSelectionSet rightFields)⟩)])]
          []) }
  have hmergedShapeRaw :
      mergedRawShape
        =
          { fields :=
            [(parentResponseName,
              [(parentHeader,
                ⟨LeafField.toShapeFields rawChildCondition
                  (leftFields ++ rightFields)⟩)])] } := by
    dsimp [mergedRawShape]
    rw [hleftFieldShape, hrightFieldShape]
    have hrightNil :
        ResponseShape.Shape.mergeFields
          [(parentResponseName,
            [(parentHeader,
              ⟨LeafField.toShapeFields rawChildCondition rightFields⟩)])]
          []
          =
            [(parentResponseName,
              [(parentHeader,
                ⟨LeafField.toShapeFields rawChildCondition rightFields⟩)])] := by
      simp [ResponseShape.Shape.mergeFields, ResponseShape.Shape.merge,
        ResponseShape.Shape.size, ResponseShape.Shape.fieldsSize,
        ResponseShape.Shape.variantsSize,
        ResponseShape.Shape.mergeWithFuel,
        ResponseShape.Shape.mergeFieldsWithFuel]
      cases (1 + (1 + ResponseShape.Shape.fieldsSize
        (LeafField.toShapeFields rawChildCondition rightFields))) <;>
        simp [ResponseShape.Shape.mergeFieldsWithFuel]
    have hmerge :=
      LeafField.mergeFields_parentVariant_childShapeFields_append parentResponseName
        parentHeader rawChildCondition leftFields rightFields hchildNodup
    rw [hrightNil]
    exact congrArg (fun fields => ({ fields := fields } : ResponseShape.Shape)) hmerge
  have htopFuel :
      1 + leftFields.length + (1 + rightFields.length)
        = (leftFields.length + rightFields.length + 1) + 1 := by
    omega
  have hcompletionFuel :
      (1 + leftFields.length + (1 + rightFields.length)) * 3
        =
          ((1 + leftFields.length + (1 + rightFields.length)) * 3 - 2) + 2 := by
    omega
  have hcompletionFuelTop :
      (leftFields.length + rightFields.length + 1 + 1) * 3
        =
          ((leftFields.length + rightFields.length + 1 + 1) * 3 - 2) + 2 := by
    omega
  cases hresolved :
      store.resolveValue parentFieldName parentArguments
        (Value.object root.typeName root.id) with
  | null =>
      simp [TypedExecution.executeSemanticQuery, Execution.executeSemanticQueryFuel,
        Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
        LeafField.toSelectionSet_size, TypedExecution.executeSelectionSet,
        Execution.collectFields, Execution.collectSelection,
        Execution.selectionDirectivesAllowBool, Execution.mergeExecutableGroups,
        Execution.addExecutableGroup, Execution.addExecutableFields,
        Execution.addExecutableField, Execution.mergedFieldSelectionSet,
        TypedExecution.executeCollectedFields, TypedExecution.executeField,
        TypedExecution.completeValue, hresolved,
        ResponseShape.Shape.ofSemanticOperation,
        ResponseShape.Shape.semanticOperationShapeFuel,
        ResponseShape.Shape.semanticSelectionSetShape,
        ResponseShape.Shape.collectSelectionSetShapeFields,
        ResponseShape.Shape.collectSelectionShapeFields,
        LeafField.collectSelectionSetShapeFields_toSelectionSet,
        ResponseShape.Condition.fromDirectives?, ResponseShape.Condition.empty,
        ResponseShape.Condition.satisfiableBool,
        ResponseShape.Condition.hasContradictionBool,
        ResponseShape.BooleanLiteral.hasContradictionBool,
        ResponseShape.Condition.possibleTypesEmptyBool,
        ResponseShape.Condition.and, ResponseShape.Condition.forChildType,
        ResponseShape.Shape.semanticOperationInitialCondition, hrootPossibleNonempty,
        hchildNonempty, hparentField, hparentNamed, Schema.fieldReturnType?,
        TypeRef.namedType, childCondition]
      change typedResponseConformsToShapeBool variableValues
        (1 + leftFields.length + (1 + rightFields.length) + 1)
        (TypedResponse.object root.typeName
          [(parentResponseName,
            TypedExecution.completeValue schema store variableValues
              ((1 + leftFields.length + (1 + rightFields.length)) * 3) childType
              (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
              Value.null)])
        mergedRawShape = true
      rw [hmergedShapeRaw]
      rw [htopFuel]
      change typedFieldsConformToShapeBool variableValues
        (leftFields.length + rightFields.length + 1 + 1) root.typeName
        [(parentResponseName,
          TypedExecution.completeValue schema store variableValues
            ((leftFields.length + rightFields.length + 1 + 1) * 3)
            childType
            (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
            Value.null)]
        { fields :=
          [(parentResponseName,
            [(parentHeader,
              ⟨LeafField.toShapeFields rawChildCondition
                (leftFields ++ rightFields)⟩)])] } = true
      have hparentActive :
          variantHeaderActiveBool variableValues root.typeName parentHeader = true := by
        simp [parentHeader, variantHeaderActiveBool, conditionHoldsBool,
          possibleTypesHoldBool_of_typeIncludesObject schema hrootType]
      have hchildNull :
          typedResponseConformsToShapeBool variableValues
            (leftFields.length + rightFields.length)
            (TypedExecution.completeValue schema store variableValues
              ((leftFields.length + rightFields.length + 1 + 1) * 3)
              childType
              (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
              Value.null)
            ⟨LeafField.toShapeFields rawChildCondition
              (leftFields ++ rightFields)⟩ = true := by
        have hcompleteNull :
            TypedExecution.completeValue schema store variableValues
              ((leftFields.length + rightFields.length + 1 + 1) * 3)
              childType
              (LeafField.toSelectionSet leftFields ++
                LeafField.toSelectionSet rightFields)
              Value.null = TypedResponse.null := by
          cases ((leftFields.length + rightFields.length + 1 + 1) * 3) <;>
            simp [TypedExecution.completeValue, shallowTypedResponse]
        have hnullConforms :
            typedResponseConformsToShapeBool variableValues
              (leftFields.length + rightFields.length) TypedResponse.null
              ⟨LeafField.toShapeFields rawChildCondition
                (leftFields ++ rightFields)⟩ = true := by
          cases (leftFields.length + rightFields.length) <;>
            simp [typedResponseConformsToShapeBool]
        simpa [hcompleteNull] using hnullConforms
      have hvariant :
          typedVariantConformsToShapeBool variableValues
            (leftFields.length + rightFields.length + 1) root.typeName
            (TypedExecution.completeValue schema store variableValues
              ((leftFields.length + rightFields.length + 1 + 1) * 3)
              childType
              (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
              Value.null)
            [(parentHeader,
              ⟨LeafField.toShapeFields rawChildCondition
                (leftFields ++ rightFields)⟩)] = true :=
        typedVariantConformsToShapeBool_singleton variableValues
          (leftFields.length + rightFields.length) root.typeName
          (TypedExecution.completeValue schema store variableValues
            ((leftFields.length + rightFields.length + 1 + 1) * 3)
            childType
            (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
            Value.null)
          parentHeader
          ⟨LeafField.toShapeFields rawChildCondition
            (leftFields ++ rightFields)⟩
          hparentActive hchildNull
      exact typedFieldsConformToShapeBool_singleton variableValues
        (leftFields.length + rightFields.length + 1) root.typeName parentResponseName
        (TypedExecution.completeValue schema store variableValues
          ((leftFields.length + rightFields.length + 1 + 1) * 3)
          childType
          (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
          Value.null)
        [(parentHeader,
          ⟨LeafField.toShapeFields rawChildCondition
            (leftFields ++ rightFields)⟩)]
        hvariant
  | scalar value =>
      exact False.elim (hnotScalar value hresolved)
  | object runtimeType id =>
      have hconforms :
          Value.conformsToType schema (.object runtimeType id)
            parentFieldDefinition.outputType := by
        cases hresolvedConforms with
        | inl hnull =>
            rw [hresolved] at hnull
            cases hnull
        | inr hconforms =>
            simpa [hresolved] using hconforms
      have hchildType : schema.typeIncludesObject childType runtimeType :=
        object_conformsToType_typeIncludesObject schema runtimeType id childType
          parentFieldDefinition.outputType hparentNamed hconforms
      have hchildCondition :
          conditionHoldsBool variableValues runtimeType
            (ResponseShape.Condition.forChildType schema
              { possibleTypes := some (schema.getPossibleTypes rootType),
                booleanLiterals := [] }
              childType) = true := by
        exact conditionHoldsBool_forChildType schema variableValues
          (condition :=
            { possibleTypes := some (schema.getPossibleTypes rootType),
              booleanLiterals := [] })
          (by simp) hchildType
      simp [TypedExecution.executeSemanticQuery, Execution.executeSemanticQueryFuel,
        Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
        LeafField.toSelectionSet_size, TypedExecution.executeSelectionSet,
        Execution.collectFields, Execution.collectSelection,
        Execution.selectionDirectivesAllowBool, Execution.mergeExecutableGroups,
        Execution.addExecutableGroup, Execution.addExecutableFields,
        Execution.addExecutableField, Execution.mergedFieldSelectionSet,
        TypedExecution.executeCollectedFields, TypedExecution.executeField,
        TypedExecution.completeValue, hresolved,
        ResponseShape.Shape.ofSemanticOperation,
        ResponseShape.Shape.semanticOperationShapeFuel,
        ResponseShape.Shape.semanticSelectionSetShape,
        ResponseShape.Shape.collectSelectionSetShapeFields,
        ResponseShape.Shape.collectSelectionShapeFields,
        LeafField.collectSelectionSetShapeFields_toSelectionSet,
        ResponseShape.Condition.fromDirectives?, ResponseShape.Condition.empty,
        ResponseShape.Condition.satisfiableBool,
        ResponseShape.Condition.hasContradictionBool,
        ResponseShape.BooleanLiteral.hasContradictionBool,
        ResponseShape.Condition.possibleTypesEmptyBool,
        ResponseShape.Condition.and, ResponseShape.Condition.forChildType,
        ResponseShape.Shape.semanticOperationInitialCondition, hrootPossibleNonempty,
        hchildNonempty, hparentField, hparentNamed, Schema.fieldReturnType?,
        TypeRef.namedType, childCondition]
      change typedResponseConformsToShapeBool variableValues
        (1 + leftFields.length + (1 + rightFields.length) + 1)
        (TypedResponse.object root.typeName
          [(parentResponseName,
            TypedExecution.completeValue schema store variableValues
              ((1 + leftFields.length + (1 + rightFields.length)) * 3) childType
              (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
              (Value.object runtimeType id))])
        mergedRawShape = true
      rw [hmergedShapeRaw]
      rw [htopFuel]
      change typedFieldsConformToShapeBool variableValues
        (leftFields.length + rightFields.length + 1 + 1) root.typeName
        [(parentResponseName,
          TypedExecution.completeValue schema store variableValues
            ((leftFields.length + rightFields.length + 1 + 1) * 3)
            childType
            (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
            (Value.object runtimeType id))]
        { fields :=
          [(parentResponseName,
            [(parentHeader,
              ⟨LeafField.toShapeFields rawChildCondition
                (leftFields ++ rightFields)⟩)])] } = true
      have hparentActive :
          variantHeaderActiveBool variableValues root.typeName parentHeader = true := by
        simp [parentHeader, variantHeaderActiveBool, conditionHoldsBool,
          possibleTypesHoldBool_of_typeIncludesObject schema hrootType]
      have hrawChildCondition :
          conditionHoldsBool variableValues runtimeType rawChildCondition = true := by
        simpa [rawChildCondition, ResponseShape.Condition.forChildType] using
          hchildCondition
      have hvariant :
          typedVariantConformsToShapeBool variableValues
            (leftFields.length + rightFields.length + 1) root.typeName
            (TypedExecution.completeValue schema store variableValues
              ((leftFields.length + rightFields.length + 1 + 1) * 3)
              childType
              (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
              (Value.object runtimeType id))
            [(parentHeader,
              ⟨LeafField.toShapeFields rawChildCondition
                (leftFields ++ rightFields)⟩)] = true := by
        rw [hcompletionFuelTop]
        simpa [LeafField.toSelectionSet_append] using
          LeafField.typedVariantConformsToShape_parentObjectSelectionSetAnyFuel schema
            store variableValues (leftFields.length + rightFields.length)
            ((leftFields.length + rightFields.length + 1 + 1) * 3 - 2)
            root.typeName childType runtimeType id parentHeader rawChildCondition
            (leftFields ++ rightFields) hchildNodup hparentActive
            hrawChildCondition
      exact typedFieldsConformToShapeBool_singleton variableValues
        (leftFields.length + rightFields.length + 1) root.typeName parentResponseName
        (TypedExecution.completeValue schema store variableValues
          ((leftFields.length + rightFields.length + 1 + 1) * 3)
          childType
          (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
          (Value.object runtimeType id))
        [(parentHeader,
          ⟨LeafField.toShapeFields rawChildCondition
            (leftFields ++ rightFields)⟩)]
        hvariant
  | list values =>
      cases hresolvedConforms with
      | inl hnull =>
          rw [hresolved] at hnull
          cases hnull
      | inr hconforms =>
          exact False.elim
            ((hlistImpossible values) (by simpa [hresolved] using hconforms))

theorem responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeLeafFieldsNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName childType : Name)
    (parentArguments : List Argument)
    (leftFields rightFields : List LeafField)
    (rootObject : ObjectType) (parentFieldDefinition : FieldDefinition) :
    schema.lookupType rootType = some (.object rootObject) ->
      schema.lookupField rootType parentFieldName = some parentFieldDefinition ->
      parentFieldDefinition.outputType = .named childType ->
      ¬ schema.getPossibleTypes childType = [] ->
      LeafField.responseNamesNodup (leftFields ++ rightFields) ->
        responseShapeCorrectForTypedExecutionAtRoot schema
          { name := name,
            rootType := rootType,
            variableDefinitions := variableDefinitions,
            selectionSet := [
              .field parentResponseName parentFieldName parentArguments []
                (LeafField.toSelectionSet leftFields),
              .field parentResponseName parentFieldName parentArguments []
                (LeafField.toSelectionSet rightFields)
            ] } := by
  intro hrootObject hparentField hparentOutput hchildNonempty hchildNodup
  exact
    responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeLeafFieldsNoDirectives_ofObjectOutput
      schema name rootType variableDefinitions parentResponseName parentFieldName childType
      parentArguments leftFields rightFields rootObject parentFieldDefinition hrootObject
      hparentField
      (by simp [hparentOutput, TypeRef.namedType])
      (by
        intro values hconforms
        simpa [hparentOutput] using hconforms)
      hchildNonempty hchildNodup

theorem responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeNonNullLeafFieldsNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName childType : Name)
    (parentArguments : List Argument)
    (leftFields rightFields : List LeafField)
    (rootObject : ObjectType) (parentFieldDefinition : FieldDefinition) :
    schema.lookupType rootType = some (.object rootObject) ->
      schema.lookupField rootType parentFieldName = some parentFieldDefinition ->
      parentFieldDefinition.outputType = .nonNull (.named childType) ->
      ¬ schema.getPossibleTypes childType = [] ->
      LeafField.responseNamesNodup (leftFields ++ rightFields) ->
        responseShapeCorrectForTypedExecutionAtRoot schema
          { name := name,
            rootType := rootType,
            variableDefinitions := variableDefinitions,
            selectionSet := [
              .field parentResponseName parentFieldName parentArguments []
                (LeafField.toSelectionSet leftFields),
              .field parentResponseName parentFieldName parentArguments []
                (LeafField.toSelectionSet rightFields)
            ] } := by
  intro hrootObject hparentField hparentOutput hchildNonempty hchildNodup
  exact
    responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeLeafFieldsNoDirectives_ofObjectOutput
      schema name rootType variableDefinitions parentResponseName parentFieldName childType
      parentArguments leftFields rightFields rootObject parentFieldDefinition hrootObject
      hparentField
      (by simp [hparentOutput, TypeRef.namedType])
      (by
        intro values hconforms
        simpa [hparentOutput] using hconforms)
      hchildNonempty hchildNodup

theorem responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName childType : Name)
    (parentArguments : List Argument)
    (leftResponseName leftFieldName : Name) (leftArguments : List Argument)
    (rightResponseName rightFieldName : Name) (rightArguments : List Argument)
    (rootObject : ObjectType) (parentFieldDefinition : FieldDefinition) :
    schema.lookupType rootType = some (.object rootObject) ->
      schema.lookupField rootType parentFieldName = some parentFieldDefinition ->
      parentFieldDefinition.outputType = .named childType ->
      ¬ schema.getPossibleTypes childType = [] ->
      leftResponseName ≠ rightResponseName ->
        responseShapeCorrectForTypedExecutionAtRoot schema
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
  intro hrootObject hparentField hparentOutput hchildNonempty hdistinct
  simpa [LeafField.toSelectionSet, LeafField.toSelection] using
    responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeLeafFieldsNoDirectives
      schema name rootType variableDefinitions parentResponseName parentFieldName childType
      parentArguments
      [LeafField.mk leftResponseName leftFieldName leftArguments]
      [LeafField.mk rightResponseName rightFieldName rightArguments]
      rootObject parentFieldDefinition hrootObject hparentField hparentOutput
      hchildNonempty
      (by
        simp [LeafField.responseNamesNodup, LeafField.responseNames,
          hdistinct])

theorem responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeNonNullDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName childType : Name)
    (parentArguments : List Argument)
    (leftResponseName leftFieldName : Name) (leftArguments : List Argument)
    (rightResponseName rightFieldName : Name) (rightArguments : List Argument)
    (rootObject : ObjectType) (parentFieldDefinition : FieldDefinition) :
    schema.lookupType rootType = some (.object rootObject) ->
      schema.lookupField rootType parentFieldName = some parentFieldDefinition ->
      parentFieldDefinition.outputType = .nonNull (.named childType) ->
      ¬ schema.getPossibleTypes childType = [] ->
      leftResponseName ≠ rightResponseName ->
        responseShapeCorrectForTypedExecutionAtRoot schema
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
  intro hrootObject hparentField hparentOutput hchildNonempty hdistinct
  simpa [LeafField.toSelectionSet, LeafField.toSelection] using
    responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeNonNullLeafFieldsNoDirectives
      schema name rootType variableDefinitions parentResponseName parentFieldName childType
      parentArguments
      [LeafField.mk leftResponseName leftFieldName leftArguments]
      [LeafField.mk rightResponseName rightFieldName rightArguments]
      rootObject parentFieldDefinition hrootObject hparentField hparentOutput
      hchildNonempty
      (by
        simp [LeafField.responseNamesNodup, LeafField.responseNames,
          hdistinct])

set_option linter.unusedSimpArgs false in
theorem responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeLeafFieldsNoDirectives_ofListOutput
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName childType : Name)
    (parentArguments : List Argument)
    (leftFields rightFields : List LeafField)
    (rootObject : ObjectType) (parentFieldDefinition : FieldDefinition) :
    schema.lookupType rootType = some (.object rootObject) ->
      schema.lookupField rootType parentFieldName = some parentFieldDefinition ->
      parentFieldDefinition.outputType.namedType = childType ->
      (∀ runtimeType id,
        ¬ Value.conformsToType schema (.object runtimeType id)
          parentFieldDefinition.outputType) ->
      (∀ values,
        Value.conformsToType schema (.list values) parentFieldDefinition.outputType ->
          ∀ value, value ∈ values -> Value.conformsToType schema value (.named childType)) ->
      ¬ schema.getPossibleTypes childType = [] ->
      LeafField.responseNamesNodup (leftFields ++ rightFields) ->
        responseShapeCorrectForTypedExecutionAtRoot schema
          { name := name,
            rootType := rootType,
            variableDefinitions := variableDefinitions,
            selectionSet := [
              .field parentResponseName parentFieldName parentArguments []
                (LeafField.toSelectionSet leftFields),
              .field parentResponseName parentFieldName parentArguments []
                (LeafField.toSelectionSet rightFields)
            ] } := by
  intro hrootObject hparentField hparentNamed hobjectImpossible hvaluesFromList
    hchildNonempty hchildNodup store variableValues root hstore _hroot hrootType
  have hrootEq : root.typeName = rootType :=
    typeIncludesObject_eq_of_lookupObjectType schema hrootObject hrootType
  have hrootPossibleNonempty : ¬ schema.getPossibleTypes rootType = [] :=
    possibleTypes_nonempty_of_typeIncludesObject schema hrootType
  have hparentFieldRoot :
      schema.lookupField root.typeName parentFieldName = some parentFieldDefinition := by
    simpa [hrootEq] using hparentField
  have hnotScalar :
      ∀ value,
        store.resolveValue parentFieldName parentArguments
            (Value.object root.typeName root.id) ≠ .scalar value := by
    intro value
    exact Store.resolveValue_ne_scalar_of_compositeLookupField schema store root.typeName
      root.id parentFieldName parentArguments parentFieldDefinition value hstore
      hparentFieldRoot (by simpa [hparentNamed] using hchildNonempty)
  have hresolvedConforms :
      store.resolveValue parentFieldName parentArguments
          (Value.object root.typeName root.id) = .null
        ∨ Value.conformsToType schema
          (store.resolveValue parentFieldName parentArguments
            (Value.object root.typeName root.id))
          parentFieldDefinition.outputType :=
    Store.resolveValue_conformsToLookupField schema store root.typeName root.id
      parentFieldName parentArguments parentFieldDefinition hstore hparentFieldRoot
  let childCondition : ResponseShape.Condition :=
    { possibleTypes := some (schema.getPossibleTypes childType), booleanLiterals := [] }
  have hchildConditionSat : childCondition.satisfiableBool = true := by
    simp [childCondition, ResponseShape.Condition.satisfiableBool,
      ResponseShape.Condition.hasContradictionBool,
      ResponseShape.Condition.possibleTypesEmptyBool,
      ResponseShape.BooleanLiteral.hasContradictionBool, hchildNonempty]
  have hnameParts :
      (LeafField.responseNames leftFields ++ LeafField.responseNames rightFields).Nodup := by
    simpa [LeafField.responseNamesNodup, LeafField.responseNames, List.map_append]
      using hchildNodup
  have hleftNodup : LeafField.responseNamesNodup leftFields := by
    have hparts := hnameParts
    simp [List.nodup_append] at hparts
    exact hparts.left
  have hrightNodup : LeafField.responseNamesNodup rightFields := by
    have hparts := hnameParts
    simp [List.nodup_append] at hparts
    exact hparts.right.left
  have hleftShape :
      (match LeafField.toSelectionSet leftFields with
      | [] => ResponseShape.Shape.empty
      | _ =>
          ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema
            (1 + leftFields.length + (1 + rightFields.length)) childType
            childCondition (LeafField.toSelectionSet leftFields)⟩)
        = ⟨LeafField.toShapeFields childCondition leftFields⟩ :=
    LeafField.childShape_toSelectionSet schema
      (1 + leftFields.length + (1 + rightFields.length)) childType childCondition
      leftFields (by omega) hchildConditionSat hleftNodup
  have hrightShape :
      (match LeafField.toSelectionSet rightFields with
      | [] => ResponseShape.Shape.empty
      | _ =>
          ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema
            (1 + leftFields.length + (1 + rightFields.length)) childType
            childCondition (LeafField.toSelectionSet rightFields)⟩)
        = ⟨LeafField.toShapeFields childCondition rightFields⟩ :=
    LeafField.childShape_toSelectionSet schema
      (1 + leftFields.length + (1 + rightFields.length)) childType childCondition
      rightFields (by omega) hchildConditionSat hrightNodup
  have hleftShapeRaw :
      (match LeafField.toSelectionSet leftFields with
      | [] => ResponseShape.Shape.empty
      | _ =>
          ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema
            (1 + leftFields.length + (1 + rightFields.length)) childType
            { possibleTypes := some (schema.getPossibleTypes childType),
              booleanLiterals := [] }
            (LeafField.toSelectionSet leftFields)⟩)
        =
          ⟨LeafField.toShapeFields
            { possibleTypes := some (schema.getPossibleTypes childType),
              booleanLiterals := [] }
            leftFields⟩ := by
    simpa [childCondition] using hleftShape
  have hrightShapeRaw :
      (match LeafField.toSelectionSet rightFields with
      | [] => ResponseShape.Shape.empty
      | _ =>
          ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema
            (1 + leftFields.length + (1 + rightFields.length)) childType
            { possibleTypes := some (schema.getPossibleTypes childType),
              booleanLiterals := [] }
            (LeafField.toSelectionSet rightFields)⟩)
        =
          ⟨LeafField.toShapeFields
            { possibleTypes := some (schema.getPossibleTypes childType),
              booleanLiterals := [] }
            rightFields⟩ := by
    simpa [childCondition] using hrightShape
  let parentHeader : ResponseShape.VariantHeader :=
    Prod.mk
      (ResponseShape.Condition.mk (some (schema.getPossibleTypes rootType)) [])
      (ResponseShape.selectedField parentFieldName parentArguments)
  let rawChildCondition : ResponseShape.Condition :=
    ResponseShape.Condition.mk (some (schema.getPossibleTypes childType)) []
  have hleftFieldShape :
      [(parentResponseName,
        [(parentHeader,
          match LeafField.toSelectionSet leftFields with
          | [] => ResponseShape.Shape.empty
          | _ =>
              ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema
                (1 + leftFields.length + (1 + rightFields.length)) childType
                rawChildCondition (LeafField.toSelectionSet leftFields)⟩)])]
        =
          [(parentResponseName,
            [(parentHeader,
              ⟨LeafField.toShapeFields rawChildCondition leftFields⟩)])] := by
    simpa [parentHeader, rawChildCondition] using
      congrArg
        (fun childShape : ResponseShape.Shape =>
          [(parentResponseName, [(parentHeader, childShape)])])
        hleftShapeRaw
  have hrightFieldShape :
      [(parentResponseName,
        [(parentHeader,
          match LeafField.toSelectionSet rightFields with
          | [] => ResponseShape.Shape.empty
          | _ =>
              ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema
                (1 + leftFields.length + (1 + rightFields.length)) childType
                rawChildCondition (LeafField.toSelectionSet rightFields)⟩)])]
        =
          [(parentResponseName,
            [(parentHeader,
              ⟨LeafField.toShapeFields rawChildCondition rightFields⟩)])] := by
    simpa [parentHeader, rawChildCondition] using
      congrArg
        (fun childShape : ResponseShape.Shape =>
          [(parentResponseName, [(parentHeader, childShape)])])
        hrightShapeRaw
  let mergedRawShape : ResponseShape.Shape :=
    { fields :=
      ResponseShape.Shape.mergeFields
        [(parentResponseName,
          [(parentHeader,
            match LeafField.toSelectionSet leftFields with
            | [] => ResponseShape.Shape.empty
            | _ =>
                ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema
                  (1 + leftFields.length + (1 + rightFields.length)) childType
                  rawChildCondition (LeafField.toSelectionSet leftFields)⟩)])]
        (ResponseShape.Shape.mergeFields
          [(parentResponseName,
            [(parentHeader,
              match LeafField.toSelectionSet rightFields with
              | [] => ResponseShape.Shape.empty
              | _ =>
                  ⟨ResponseShape.Shape.collectSelectionSetShapeFields schema
                    (1 + leftFields.length + (1 + rightFields.length)) childType
                    rawChildCondition (LeafField.toSelectionSet rightFields)⟩)])]
          []) }
  have hmergedShapeRaw :
      mergedRawShape
        =
          { fields :=
            [(parentResponseName,
              [(parentHeader,
                ⟨LeafField.toShapeFields rawChildCondition
                  (leftFields ++ rightFields)⟩)])] } := by
    dsimp [mergedRawShape]
    rw [hleftFieldShape, hrightFieldShape]
    have hrightNil :
        ResponseShape.Shape.mergeFields
          [(parentResponseName,
            [(parentHeader,
              ⟨LeafField.toShapeFields rawChildCondition rightFields⟩)])]
          []
          =
            [(parentResponseName,
              [(parentHeader,
                ⟨LeafField.toShapeFields rawChildCondition rightFields⟩)])] := by
      simp [ResponseShape.Shape.mergeFields, ResponseShape.Shape.merge,
        ResponseShape.Shape.size, ResponseShape.Shape.fieldsSize,
        ResponseShape.Shape.variantsSize,
        ResponseShape.Shape.mergeWithFuel,
        ResponseShape.Shape.mergeFieldsWithFuel]
      cases (1 + (1 + ResponseShape.Shape.fieldsSize
        (LeafField.toShapeFields rawChildCondition rightFields))) <;>
        simp [ResponseShape.Shape.mergeFieldsWithFuel]
    have hmerge :=
      LeafField.mergeFields_parentVariant_childShapeFields_append parentResponseName
        parentHeader rawChildCondition leftFields rightFields hchildNodup
    rw [hrightNil]
    exact congrArg (fun fields => ({ fields := fields } : ResponseShape.Shape)) hmerge
  have htopFuel :
      1 + leftFields.length + (1 + rightFields.length)
        = (leftFields.length + rightFields.length + 1) + 1 := by
    omega
  cases hresolved :
      store.resolveValue parentFieldName parentArguments
        (Value.object root.typeName root.id) with
  | null =>
      simp [TypedExecution.executeSemanticQuery, Execution.executeSemanticQueryFuel,
        Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
        LeafField.toSelectionSet_size, TypedExecution.executeSelectionSet,
        Execution.collectFields, Execution.collectSelection,
        Execution.selectionDirectivesAllowBool, Execution.mergeExecutableGroups,
        Execution.addExecutableGroup, Execution.addExecutableFields,
        Execution.addExecutableField, Execution.mergedFieldSelectionSet,
        TypedExecution.executeCollectedFields, TypedExecution.executeField,
        TypedExecution.completeValue, hresolved,
        ResponseShape.Shape.ofSemanticOperation,
        ResponseShape.Shape.semanticOperationShapeFuel,
        ResponseShape.Shape.semanticSelectionSetShape,
        ResponseShape.Shape.collectSelectionSetShapeFields,
        ResponseShape.Shape.collectSelectionShapeFields,
        LeafField.collectSelectionSetShapeFields_toSelectionSet,
        ResponseShape.Condition.fromDirectives?, ResponseShape.Condition.empty,
        ResponseShape.Condition.satisfiableBool,
        ResponseShape.Condition.hasContradictionBool,
        ResponseShape.BooleanLiteral.hasContradictionBool,
        ResponseShape.Condition.possibleTypesEmptyBool,
        ResponseShape.Condition.and, ResponseShape.Condition.forChildType,
        ResponseShape.Shape.semanticOperationInitialCondition, hrootPossibleNonempty,
        hchildNonempty, hparentField, hparentNamed, Schema.fieldReturnType?,
        TypeRef.namedType, childCondition]
      change typedResponseConformsToShapeBool variableValues
        (1 + leftFields.length + (1 + rightFields.length) + 1)
        (TypedResponse.object root.typeName
          [(parentResponseName,
            TypedExecution.completeValue schema store variableValues
              ((1 + leftFields.length + (1 + rightFields.length)) * 3) childType
              (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
              Value.null)])
        mergedRawShape = true
      rw [hmergedShapeRaw]
      rw [htopFuel]
      change typedFieldsConformToShapeBool variableValues
        (leftFields.length + rightFields.length + 1 + 1) root.typeName
        [(parentResponseName,
          TypedExecution.completeValue schema store variableValues
            ((leftFields.length + rightFields.length + 1 + 1) * 3)
            childType
            (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
            Value.null)]
        { fields :=
          [(parentResponseName,
            [(parentHeader,
              ⟨LeafField.toShapeFields rawChildCondition
                (leftFields ++ rightFields)⟩)])] } = true
      have hparentActive :
          variantHeaderActiveBool variableValues root.typeName parentHeader = true := by
        simp [parentHeader, variantHeaderActiveBool, conditionHoldsBool,
          possibleTypesHoldBool_of_typeIncludesObject schema hrootType]
      have hchildNull :
          typedResponseConformsToShapeBool variableValues
            (leftFields.length + rightFields.length)
            (TypedExecution.completeValue schema store variableValues
              ((leftFields.length + rightFields.length + 1 + 1) * 3)
              childType
              (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
              Value.null)
            ⟨LeafField.toShapeFields rawChildCondition
              (leftFields ++ rightFields)⟩ = true := by
        have hcompleteNull :
            TypedExecution.completeValue schema store variableValues
              ((leftFields.length + rightFields.length + 1 + 1) * 3)
              childType
              (LeafField.toSelectionSet leftFields ++
                LeafField.toSelectionSet rightFields)
              Value.null = TypedResponse.null := by
          cases ((leftFields.length + rightFields.length + 1 + 1) * 3) <;>
            simp [TypedExecution.completeValue, shallowTypedResponse]
        have hnullConforms :
            typedResponseConformsToShapeBool variableValues
              (leftFields.length + rightFields.length) TypedResponse.null
              ⟨LeafField.toShapeFields rawChildCondition
                (leftFields ++ rightFields)⟩ = true := by
          cases (leftFields.length + rightFields.length) <;>
            simp [typedResponseConformsToShapeBool]
        simpa [hcompleteNull] using hnullConforms
      have hvariant :
          typedVariantConformsToShapeBool variableValues
            (leftFields.length + rightFields.length + 1) root.typeName
            (TypedExecution.completeValue schema store variableValues
              ((leftFields.length + rightFields.length + 1 + 1) * 3)
              childType
              (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
              Value.null)
            [(parentHeader,
              ⟨LeafField.toShapeFields rawChildCondition
                (leftFields ++ rightFields)⟩)] = true :=
        typedVariantConformsToShapeBool_singleton variableValues
          (leftFields.length + rightFields.length) root.typeName
          (TypedExecution.completeValue schema store variableValues
            ((leftFields.length + rightFields.length + 1 + 1) * 3)
            childType
            (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
            Value.null)
          parentHeader
          ⟨LeafField.toShapeFields rawChildCondition
            (leftFields ++ rightFields)⟩
          hparentActive hchildNull
      exact typedFieldsConformToShapeBool_singleton variableValues
        (leftFields.length + rightFields.length + 1) root.typeName parentResponseName
        (TypedExecution.completeValue schema store variableValues
          ((leftFields.length + rightFields.length + 1 + 1) * 3)
          childType
          (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
          Value.null)
        [(parentHeader,
          ⟨LeafField.toShapeFields rawChildCondition
            (leftFields ++ rightFields)⟩)]
        hvariant
  | scalar value =>
      exact False.elim (hnotScalar value hresolved)
  | object runtimeType id =>
      cases hresolvedConforms with
      | inl hnull =>
          rw [hresolved] at hnull
          cases hnull
      | inr hconforms =>
          exact False.elim
            ((hobjectImpossible runtimeType id) (by simpa [hresolved] using hconforms))
  | list values =>
      have hvaluesConform :
          ∀ value, value ∈ values ->
            Value.conformsToType schema value (.named childType) := by
        cases hresolvedConforms with
        | inl hnull =>
            rw [hresolved] at hnull
            cases hnull
        | inr hconforms =>
            exact hvaluesFromList values (by simpa [hresolved] using hconforms)
      simp [TypedExecution.executeSemanticQuery, Execution.executeSemanticQueryFuel,
        Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
        LeafField.toSelectionSet_size, TypedExecution.executeSelectionSet,
        Execution.collectFields, Execution.collectSelection,
        Execution.selectionDirectivesAllowBool, Execution.mergeExecutableGroups,
        Execution.addExecutableGroup, Execution.addExecutableFields,
        Execution.addExecutableField, Execution.mergedFieldSelectionSet,
        TypedExecution.executeCollectedFields, TypedExecution.executeField,
        TypedExecution.completeValue, hresolved,
        ResponseShape.Shape.ofSemanticOperation,
        ResponseShape.Shape.semanticOperationShapeFuel,
        ResponseShape.Shape.semanticSelectionSetShape,
        ResponseShape.Shape.collectSelectionSetShapeFields,
        ResponseShape.Shape.collectSelectionShapeFields,
        LeafField.collectSelectionSetShapeFields_toSelectionSet,
        ResponseShape.Condition.fromDirectives?, ResponseShape.Condition.empty,
        ResponseShape.Condition.satisfiableBool,
        ResponseShape.Condition.hasContradictionBool,
        ResponseShape.BooleanLiteral.hasContradictionBool,
        ResponseShape.Condition.possibleTypesEmptyBool,
        ResponseShape.Condition.and, ResponseShape.Condition.forChildType,
        ResponseShape.Shape.semanticOperationInitialCondition, hrootPossibleNonempty,
        hchildNonempty, hparentField, hparentNamed, Schema.fieldReturnType?,
        TypeRef.namedType, childCondition]
      change typedResponseConformsToShapeBool variableValues
        (1 + leftFields.length + (1 + rightFields.length) + 1)
        (TypedResponse.object root.typeName
          [(parentResponseName,
            TypedExecution.completeValue schema store variableValues
              ((1 + leftFields.length + (1 + rightFields.length)) * 3) childType
              (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
              (Value.list values))])
        mergedRawShape = true
      rw [hmergedShapeRaw]
      rw [htopFuel]
      change typedFieldsConformToShapeBool variableValues
        (leftFields.length + rightFields.length + 1 + 1) root.typeName
        [(parentResponseName,
          TypedExecution.completeValue schema store variableValues
            ((leftFields.length + rightFields.length + 1 + 1) * 3)
            childType
            (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
            (Value.list values))]
        { fields :=
          [(parentResponseName,
            [(parentHeader,
              ⟨LeafField.toShapeFields rawChildCondition
                (leftFields ++ rightFields)⟩)])] } = true
      have hparentActive :
          variantHeaderActiveBool variableValues root.typeName parentHeader = true := by
        simp [parentHeader, variantHeaderActiveBool, conditionHoldsBool,
          possibleTypesHoldBool_of_typeIncludesObject schema hrootType]
      have hlistFuel :
          (leftFields.length + rightFields.length + 1 + 1) * 3
            =
              ((leftFields.length + rightFields.length + 1 + 1) * 3 - 1) + 1 := by
        omega
      have hlistElementFuel :
          ((leftFields.length + rightFields.length + 1 + 1) * 3 - 3) + 2
            =
              (leftFields.length + rightFields.length + 1 + 1) * 3 - 1 := by
        omega
      have hchildList :
          typedResponseConformsToShapeBool variableValues
            (leftFields.length + rightFields.length)
            (TypedExecution.completeValue schema store variableValues
              ((leftFields.length + rightFields.length + 1 + 1) * 3)
              childType
              (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
              (Value.list values))
            ⟨LeafField.toShapeFields rawChildCondition
              (leftFields ++ rightFields)⟩ = true := by
        rw [hlistFuel]
        cases hfuel : (leftFields.length + rightFields.length) with
        | zero =>
            simp [hfuel, TypedExecution.completeValue, typedResponseConformsToShapeBool]
        | succ childFuel =>
            have hlistConforms :
                (values.map
                  (TypedExecution.completeValue schema store variableValues
                    ((leftFields.length + rightFields.length + 1 + 1) * 3 - 1)
                    childType
                    (LeafField.toSelectionSet leftFields ++
                      LeafField.toSelectionSet rightFields))).all
                  (fun response =>
                    typedResponseConformsToShapeBool variableValues childFuel response
                      ⟨LeafField.toShapeFields rawChildCondition
                        (leftFields ++ rightFields)⟩) = true := by
              simpa [rawChildCondition, hfuel, hlistElementFuel,
                LeafField.toSelectionSet_append] using
                LeafField.typedResponseConformsToShape_completeValue_namedCompositeListSelectionSetAnyFuel
                  schema store variableValues childFuel
                  ((leftFields.length + rightFields.length + 1 + 1) * 3 - 3)
                  childType childType (leftFields ++ rightFields) values hchildNodup
                  hvaluesConform hchildNonempty
            simpa [hfuel, TypedExecution.completeValue, typedResponseConformsToShapeBool]
              using hlistConforms
      have hvariant :
          typedVariantConformsToShapeBool variableValues
            (leftFields.length + rightFields.length + 1) root.typeName
            (TypedExecution.completeValue schema store variableValues
              ((leftFields.length + rightFields.length + 1 + 1) * 3)
              childType
              (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
              (Value.list values))
            [(parentHeader,
              ⟨LeafField.toShapeFields rawChildCondition
                (leftFields ++ rightFields)⟩)] = true :=
        typedVariantConformsToShapeBool_singleton variableValues
          (leftFields.length + rightFields.length) root.typeName
          (TypedExecution.completeValue schema store variableValues
            ((leftFields.length + rightFields.length + 1 + 1) * 3)
            childType
            (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
            (Value.list values))
          parentHeader
          ⟨LeafField.toShapeFields rawChildCondition
            (leftFields ++ rightFields)⟩
          hparentActive hchildList
      exact typedFieldsConformToShapeBool_singleton variableValues
        (leftFields.length + rightFields.length + 1) root.typeName parentResponseName
        (TypedExecution.completeValue schema store variableValues
          ((leftFields.length + rightFields.length + 1 + 1) * 3)
          childType
          (LeafField.toSelectionSet leftFields ++ LeafField.toSelectionSet rightFields)
          (Value.list values))
        [(parentHeader,
          ⟨LeafField.toShapeFields rawChildCondition
            (leftFields ++ rightFields)⟩)]
        hvariant

theorem responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeListLeafFieldsNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName childType : Name)
    (parentArguments : List Argument)
    (leftFields rightFields : List LeafField)
    (rootObject : ObjectType) (parentFieldDefinition : FieldDefinition) :
    schema.lookupType rootType = some (.object rootObject) ->
      schema.lookupField rootType parentFieldName = some parentFieldDefinition ->
      parentFieldDefinition.outputType = .list (.named childType) ->
      ¬ schema.getPossibleTypes childType = [] ->
      LeafField.responseNamesNodup (leftFields ++ rightFields) ->
        responseShapeCorrectForTypedExecutionAtRoot schema
          { name := name,
            rootType := rootType,
            variableDefinitions := variableDefinitions,
            selectionSet := [
              .field parentResponseName parentFieldName parentArguments []
                (LeafField.toSelectionSet leftFields),
              .field parentResponseName parentFieldName parentArguments []
                (LeafField.toSelectionSet rightFields)
            ] } := by
  intro hrootObject hparentField hparentOutput hchildNonempty hchildNodup
  exact
    responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeLeafFieldsNoDirectives_ofListOutput
      schema name rootType variableDefinitions parentResponseName parentFieldName childType
      parentArguments leftFields rightFields rootObject parentFieldDefinition hrootObject
      hparentField
      (by simp [hparentOutput, TypeRef.namedType])
      (by
        intro runtimeType id hconforms
        simpa [hparentOutput] using hconforms)
      (by
        intro values hconforms
        simpa [hparentOutput] using hconforms)
      hchildNonempty hchildNodup

theorem responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeNonNullListLeafFieldsNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName childType : Name)
    (parentArguments : List Argument)
    (leftFields rightFields : List LeafField)
    (rootObject : ObjectType) (parentFieldDefinition : FieldDefinition) :
    schema.lookupType rootType = some (.object rootObject) ->
      schema.lookupField rootType parentFieldName = some parentFieldDefinition ->
      parentFieldDefinition.outputType = .nonNull (.list (.named childType)) ->
      ¬ schema.getPossibleTypes childType = [] ->
      LeafField.responseNamesNodup (leftFields ++ rightFields) ->
        responseShapeCorrectForTypedExecutionAtRoot schema
          { name := name,
            rootType := rootType,
            variableDefinitions := variableDefinitions,
            selectionSet := [
              .field parentResponseName parentFieldName parentArguments []
                (LeafField.toSelectionSet leftFields),
              .field parentResponseName parentFieldName parentArguments []
                (LeafField.toSelectionSet rightFields)
            ] } := by
  intro hrootObject hparentField hparentOutput hchildNonempty hchildNodup
  exact
    responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeLeafFieldsNoDirectives_ofListOutput
      schema name rootType variableDefinitions parentResponseName parentFieldName childType
      parentArguments leftFields rightFields rootObject parentFieldDefinition hrootObject
      hparentField
      (by simp [hparentOutput, TypeRef.namedType])
      (by
        intro runtimeType id hconforms
        simpa [hparentOutput] using hconforms)
      (by
        intro values hconforms
        simpa [hparentOutput] using hconforms)
      hchildNonempty hchildNodup

set_option linter.unusedSimpArgs false in
theorem responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeListDistinctLeafNoDirectives_ofListOutput
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName childType : Name)
    (parentArguments : List Argument)
    (leftResponseName leftFieldName : Name) (leftArguments : List Argument)
    (rightResponseName rightFieldName : Name) (rightArguments : List Argument)
    (rootObject : ObjectType) (parentFieldDefinition : FieldDefinition) :
    schema.lookupType rootType = some (.object rootObject) ->
      schema.lookupField rootType parentFieldName = some parentFieldDefinition ->
      parentFieldDefinition.outputType.namedType = childType ->
      (∀ runtimeType id,
        ¬ Value.conformsToType schema (.object runtimeType id)
          parentFieldDefinition.outputType) ->
      (∀ values,
        Value.conformsToType schema (.list values) parentFieldDefinition.outputType ->
          ∀ value, value ∈ values -> Value.conformsToType schema value (.named childType)) ->
      ¬ schema.getPossibleTypes childType = [] ->
      leftResponseName ≠ rightResponseName ->
        responseShapeCorrectForTypedExecutionAtRoot schema
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
  intro hrootObject hparentField hparentNamed hobjectImpossible hvaluesFromList
    hchildNonempty hdistinct store
    variableValues root hstore _hroot hrootType
  have hdistinct' : rightResponseName ≠ leftResponseName := Ne.symm hdistinct
  have hrootEq : root.typeName = rootType :=
    typeIncludesObject_eq_of_lookupObjectType schema hrootObject hrootType
  have hrootPossibleNonempty : ¬ schema.getPossibleTypes rootType = [] :=
    possibleTypes_nonempty_of_typeIncludesObject schema hrootType
  have hparentFieldRoot :
      schema.lookupField root.typeName parentFieldName = some parentFieldDefinition := by
    simpa [hrootEq] using hparentField
  have hnotScalar :
      ∀ value,
        store.resolveValue parentFieldName parentArguments
            (Value.object root.typeName root.id) ≠ .scalar value := by
    intro value
    exact Store.resolveValue_ne_scalar_of_compositeLookupField schema store root.typeName
      root.id parentFieldName parentArguments parentFieldDefinition value hstore
      hparentFieldRoot (by simpa [hparentNamed] using hchildNonempty)
  have hresolvedConforms :
      store.resolveValue parentFieldName parentArguments
          (Value.object root.typeName root.id) = .null
        ∨ Value.conformsToType schema
          (store.resolveValue parentFieldName parentArguments
            (Value.object root.typeName root.id))
          parentFieldDefinition.outputType :=
    Store.resolveValue_conformsToLookupField schema store root.typeName root.id
      parentFieldName parentArguments parentFieldDefinition hstore hparentFieldRoot
  cases hresolved :
      store.resolveValue parentFieldName parentArguments
        (Value.object root.typeName root.id) with
  | null =>
      simp [TypedExecution.executeSemanticQuery, Execution.executeSemanticQueryFuel,
        Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
        TypedExecution.executeSelectionSet, Execution.collectFields,
        Execution.collectSelection, Execution.selectionDirectivesAllowBool,
        Execution.mergeExecutableGroups, Execution.addExecutableGroup,
        Execution.addExecutableFields, Execution.addExecutableField,
        Execution.mergedFieldSelectionSet, TypedExecution.executeCollectedFields,
        TypedExecution.executeField, TypedExecution.completeValue, hresolved,
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
        ResponseShape.Condition.and, ResponseShape.Condition.forChildType,
        ResponseShape.Shape.semanticOperationInitialCondition, hrootPossibleNonempty,
        hchildNonempty, hdistinct, hdistinct', hparentField, hparentNamed,
        Schema.fieldReturnType?, TypeRef.namedType,
        LeafField.mergeFields_parentVariant_twoChildShapeFields,
        ResponseShape.Shape.mergeFields,
        ResponseShape.Shape.merge, ResponseShape.Shape.size,
        ResponseShape.Shape.fieldsSize, ResponseShape.Shape.variantsSize,
        ResponseShape.Shape.mergeWithFuel, ResponseShape.Shape.mergeFieldsWithFuel,
        ResponseShape.Shape.mergeVariantsWithFuel,
        ResponseShape.VariantHeader.eqBool_self, typedResponseConformsToShapeBool,
        typedFieldsConformToShapeBool, typedVariantConformsToShapeBool,
        variantHeaderActiveBool, conditionHoldsBool,
        possibleTypesHoldBool_of_typeIncludesObject schema hrootType,
        ResponseShape.Shape.lookupField]
  | scalar value =>
      exact False.elim (hnotScalar value hresolved)
  | object runtimeType id =>
      cases hresolvedConforms with
      | inl hnull =>
          rw [hresolved] at hnull
          cases hnull
      | inr hconforms =>
          exact False.elim
            ((hobjectImpossible runtimeType id) (by simpa [hresolved] using hconforms))
  | list values =>
      have hvaluesConform :
          ∀ value, value ∈ values ->
            Value.conformsToType schema value (.named childType) := by
        cases hresolvedConforms with
        | inl hnull =>
            rw [hresolved] at hnull
            cases hnull
        | inr hconforms =>
            exact hvaluesFromList values (by simpa [hresolved] using hconforms)
      have hlistConforms :
          (values.map
            (TypedExecution.completeValue schema store variableValues 11 childType
              [
                .field leftResponseName leftFieldName leftArguments [] [],
                .field rightResponseName rightFieldName rightArguments [] []
              ])).all
            (fun response =>
              typedResponseConformsToShapeBool variableValues 1 response
                { fields := [
                  (leftResponseName,
                    [(({ possibleTypes := some (schema.getPossibleTypes childType),
                          booleanLiterals := [] },
                        ResponseShape.selectedField leftFieldName leftArguments),
                      { fields := [] })]),
                  (rightResponseName,
                    [(({ possibleTypes := some (schema.getPossibleTypes childType),
                          booleanLiterals := [] },
                        ResponseShape.selectedField rightFieldName rightArguments),
                      { fields := [] })])
                ] }) = true :=
        typedResponseConformsToShapeBool_completeValue_namedComposite_listOneFuel
          schema store variableValues 11 childType childType
          [
            .field leftResponseName leftFieldName leftArguments [] [],
            .field rightResponseName rightFieldName rightArguments [] []
          ]
          { fields := [
            (leftResponseName,
              [(({ possibleTypes := some (schema.getPossibleTypes childType),
                    booleanLiterals := [] },
                  ResponseShape.selectedField leftFieldName leftArguments),
                { fields := [] })]),
            (rightResponseName,
              [(({ possibleTypes := some (schema.getPossibleTypes childType),
                    booleanLiterals := [] },
                  ResponseShape.selectedField rightFieldName rightArguments),
                { fields := [] })])
          ] }
          values hvaluesConform hchildNonempty
      simp [TypedExecution.executeSemanticQuery, Execution.executeSemanticQueryFuel,
        Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
        TypedExecution.executeSelectionSet, Execution.collectFields,
        Execution.collectSelection, Execution.selectionDirectivesAllowBool,
        Execution.mergeExecutableGroups, Execution.addExecutableGroup,
        Execution.addExecutableFields, Execution.addExecutableField,
        Execution.mergedFieldSelectionSet, TypedExecution.executeCollectedFields,
        TypedExecution.executeField, TypedExecution.completeValue, hresolved,
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
        ResponseShape.Condition.and, ResponseShape.Condition.forChildType,
        ResponseShape.Shape.semanticOperationInitialCondition, hrootPossibleNonempty,
        hchildNonempty, hdistinct, hdistinct', hparentField, hparentNamed,
        Schema.fieldReturnType?, TypeRef.namedType,
        LeafField.mergeFields_parentVariant_twoChildShapeFields,
        ResponseShape.Shape.mergeFields,
        ResponseShape.Shape.merge, ResponseShape.Shape.size,
        ResponseShape.Shape.fieldsSize, ResponseShape.Shape.variantsSize,
        ResponseShape.Shape.mergeWithFuel, ResponseShape.Shape.mergeFieldsWithFuel,
        ResponseShape.Shape.mergeVariantsWithFuel,
        ResponseShape.VariantHeader.eqBool_self, typedResponseConformsToShapeBool,
        typedFieldsConformToShapeBool, typedVariantConformsToShapeBool,
        variantHeaderActiveBool, conditionHoldsBool,
        possibleTypesHoldBool_of_typeIncludesObject schema hrootType,
        hlistConforms, ResponseShape.Shape.lookupField]

theorem responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeListDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName childType : Name)
    (parentArguments : List Argument)
    (leftResponseName leftFieldName : Name) (leftArguments : List Argument)
    (rightResponseName rightFieldName : Name) (rightArguments : List Argument)
    (rootObject : ObjectType) (parentFieldDefinition : FieldDefinition) :
    schema.lookupType rootType = some (.object rootObject) ->
      schema.lookupField rootType parentFieldName = some parentFieldDefinition ->
      parentFieldDefinition.outputType = .list (.named childType) ->
      ¬ schema.getPossibleTypes childType = [] ->
      leftResponseName ≠ rightResponseName ->
        responseShapeCorrectForTypedExecutionAtRoot schema
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
  intro hrootObject hparentField hparentOutput hchildNonempty hdistinct
  simpa [LeafField.toSelectionSet, LeafField.toSelection] using
    responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeListLeafFieldsNoDirectives
      schema name rootType variableDefinitions parentResponseName parentFieldName childType
      parentArguments
      [LeafField.mk leftResponseName leftFieldName leftArguments]
      [LeafField.mk rightResponseName rightFieldName rightArguments]
      rootObject parentFieldDefinition hrootObject hparentField hparentOutput
      hchildNonempty
      (by
        simp [LeafField.responseNamesNodup, LeafField.responseNames,
          hdistinct])

theorem responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeNonNullListDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (parentResponseName parentFieldName childType : Name)
    (parentArguments : List Argument)
    (leftResponseName leftFieldName : Name) (leftArguments : List Argument)
    (rightResponseName rightFieldName : Name) (rightArguments : List Argument)
    (rootObject : ObjectType) (parentFieldDefinition : FieldDefinition) :
    schema.lookupType rootType = some (.object rootObject) ->
      schema.lookupField rootType parentFieldName = some parentFieldDefinition ->
      parentFieldDefinition.outputType = .nonNull (.list (.named childType)) ->
      ¬ schema.getPossibleTypes childType = [] ->
      leftResponseName ≠ rightResponseName ->
        responseShapeCorrectForTypedExecutionAtRoot schema
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
  intro hrootObject hparentField hparentOutput hchildNonempty hdistinct
  simpa [LeafField.toSelectionSet, LeafField.toSelection] using
    responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeNonNullListLeafFieldsNoDirectives
      schema name rootType variableDefinitions parentResponseName parentFieldName childType
      parentArguments
      [LeafField.mk leftResponseName leftFieldName leftArguments]
      [LeafField.mk rightResponseName rightFieldName rightArguments]
      rootObject parentFieldDefinition hrootObject hparentField hparentOutput
      hchildNonempty
      (by
        simp [LeafField.responseNamesNodup, LeafField.responseNames,
          hdistinct])

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
