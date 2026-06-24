import GraphQL.Execution
import GraphQL.Execution.ResolverValue
import GraphQL.SchemaWellFormedness

/-! GraphQL operation normal forms -/
namespace GraphQL

namespace NormalForm

-----------------------------------------------------------------------------------------
-- Ground Type Normalization
-----------------------------------------------------------------------------------------

-- Spec 5.5.2.3 `GetPossibleTypes` helper for deciding whether an already-unwrapped
-- named return type can be normalized directly, or must be grounded through object cases.
def objectTypeNameBool (schema : Schema) (typeName : Name) : Bool :=
  match schema.lookupType typeName with
  | some (.object _) => true
  | _ => false

-- Spec 6.3.2 `CollectSubfields` analogue over selections, written
-- structurally so termination and size reasoning can reduce it directly.
def mergeSelectionSets : List Selection -> List Selection
  | [] => []
  | selection :: rest => selection.subselections ++ mergeSelectionSets rest

section NormalizeSelectionSetTermination

/-! Private termination support for `normalizeSelectionSet`. -/

private theorem selectionSet_size_append (left right : List Selection) :
    SelectionSet.size (left ++ right)
      = SelectionSet.size left + SelectionSet.size right := by
  induction left with
  | nil => simp [SelectionSet.size]
  | cons selection rest ih =>
      simp [SelectionSet.size, ih, Nat.add_assoc]

private theorem mergeSelectionSets_append
    (left right : List Selection) :
    mergeSelectionSets (left ++ right)
      = mergeSelectionSets left ++ mergeSelectionSets right := by
  induction left with
  | nil => simp [mergeSelectionSets]
  | cons selection rest ih =>
      simp [mergeSelectionSets, ih, List.append_assoc]

mutual
  -- Spec 6.3.2 field collection helper: finds fields with one response name, descending
  -- through inline fragments that can contribute selections in the current type scope.
  def validFieldsWithResponseName (schema : Schema)
      (parentType responseName : Name) :
      List Selection -> List Selection
    | [] => []
    | selection :: rest =>
        match selection with
        | .field fieldResponseName _fieldName _arguments _directives _selectionSet =>
            let restFields :=
              validFieldsWithResponseName schema parentType responseName rest
            if fieldResponseName == responseName then
              selection :: restFields
            else
              restFields
        | .inlineFragment none _directives selectionSet =>
            validFieldsWithResponseName schema parentType responseName selectionSet
              ++ validFieldsWithResponseName schema parentType responseName rest
        | .inlineFragment (some typeCondition) _directives selectionSet =>
            let restFields :=
              validFieldsWithResponseName schema parentType responseName rest
            if schema.typesOverlapBool parentType typeCondition then
              validFieldsWithResponseName schema parentType responseName selectionSet
                ++ restFields
            else
              restFields

  -- Spec 6.3.2 field collection helper: removes fields with one response name recursively
  -- so later fragment lifting cannot reintroduce a duplicate field group.
  def withoutFieldsWithResponseName (schema : Schema)
      (responseName : Name) :
      List Selection -> List Selection
    | [] => []
    | selection :: rest =>
        match selection with
        | .field fieldResponseName _fieldName _arguments _directives _selectionSet =>
            let filteredRest :=
              withoutFieldsWithResponseName schema responseName rest
            if fieldResponseName == responseName then
              filteredRest
            else
              selection :: filteredRest
        | .inlineFragment typeCondition directives selectionSet =>
            .inlineFragment typeCondition directives
              (withoutFieldsWithResponseName schema responseName selectionSet)
              :: withoutFieldsWithResponseName schema responseName rest
end

private theorem size_withoutFieldsWithResponseName_le (schema : Schema)
    (responseName : Name) :
    ∀ selectionSet,
      SelectionSet.size
          (withoutFieldsWithResponseName schema responseName selectionSet)
        ≤ SelectionSet.size selectionSet
  | [] => by
      simp [withoutFieldsWithResponseName, SelectionSet.size]
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hrest :=
            size_withoutFieldsWithResponseName_le schema responseName rest
          by_cases h : (fieldResponseName == responseName) = true
          · simp [withoutFieldsWithResponseName, h, SelectionSet.size,
              Selection.size]
            omega
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldsWithResponseName, hfalse, SelectionSet.size,
              Selection.size]
            omega
      | inlineFragment typeCondition directives selectionSet =>
          have hselectionSet :=
            size_withoutFieldsWithResponseName_le schema responseName selectionSet
          have hrest :=
            size_withoutFieldsWithResponseName_le schema responseName rest
          cases typeCondition <;>
            simp [withoutFieldsWithResponseName, SelectionSet.size,
              Selection.size]
          all_goals omega
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

private theorem size_mergeSelectionSets_validFieldsWithResponseName_le
    (schema : Schema) (parentType responseName : Name) :
    ∀ selectionSet,
      SelectionSet.size
          (mergeSelectionSets
            (validFieldsWithResponseName schema parentType responseName selectionSet))
        ≤ SelectionSet.size selectionSet
  | [] => by
      simp [validFieldsWithResponseName, mergeSelectionSets,
        SelectionSet.size]
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hrest :=
            size_mergeSelectionSets_validFieldsWithResponseName_le
              schema parentType responseName rest
          by_cases h : (fieldResponseName == responseName) = true
          · simp [validFieldsWithResponseName, mergeSelectionSets, h,
              selectionSet_size_append, SelectionSet.size,
              Selection.size, Selection.subselections]
            omega
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [validFieldsWithResponseName, hfalse,
              SelectionSet.size, Selection.size]
            omega
      | inlineFragment typeCondition directives selectionSet =>
          have hselectionSet :=
            size_mergeSelectionSets_validFieldsWithResponseName_le
              schema parentType responseName selectionSet
          have hrest :=
            size_mergeSelectionSets_validFieldsWithResponseName_le
              schema parentType responseName rest
          cases typeCondition with
          | none =>
              simp [validFieldsWithResponseName, mergeSelectionSets_append,
                selectionSet_size_append, SelectionSet.size,
                Selection.size]
              omega
          | some typeCondition =>
              by_cases h : (schema.typesOverlapBool parentType typeCondition) = true
              · simp [validFieldsWithResponseName, h, mergeSelectionSets_append,
                  selectionSet_size_append, SelectionSet.size,
                  Selection.size]
                omega
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition = false := by
                  cases hmatch : schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [validFieldsWithResponseName, hfalse, SelectionSet.size,
                  Selection.size]
                omega
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

end NormalizeSelectionSetTermination

-- Normalized fields are retained even when a composite child selection normalizes to
-- empty; execution still produces the parent response name with an empty object.
def normalizedField
    (_schema : Schema) (_returnType responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (normalizedSubselections : List Selection) : Selection :=
  .field responseName fieldName arguments directives normalizedSubselections

-- Spec 5.3.2 field merging / 6.3.2 subfield collection: total normalizer; merges
-- same-response-name fields, recursively normalizes child selections, and grounds
-- abstract field return types through possible object types. This is terminating by
-- selection-set size.
def normalizeSelectionSet (schema : Schema) (parentType : Name) :
    List Selection -> List Selection
  | [] => []
  | selection :: rest =>
      match selection with
      | .field responseName fieldName arguments directives subselections =>
          let normalizedRest :=
            normalizeSelectionSet schema parentType
              (withoutFieldsWithResponseName schema responseName rest)
          match schema.lookupField parentType fieldName with
          | none => normalizedRest
          | some fieldDefinition =>
              let matching :=
                validFieldsWithResponseName schema parentType responseName rest
              let mergedSubselections :=
                subselections ++ mergeSelectionSets matching
              let returnType := fieldDefinition.outputType.namedType
              let normalizedSubselections :=
                if objectTypeNameBool schema returnType then
                  normalizeSelectionSet schema returnType mergedSubselections
                else
                  (schema.getPossibleTypes returnType).filterMap
                    (fun objectType =>
                      match normalizeSelectionSet schema objectType
                          mergedSubselections with
                      | [] => none
                      | selection :: rest =>
                          some (.inlineFragment (some objectType) []
                            (selection :: rest)))
              normalizedField schema returnType responseName fieldName
                arguments directives normalizedSubselections :: normalizedRest
      | .inlineFragment none _directives subselections =>
          normalizeSelectionSet schema parentType (subselections ++ rest)
      | .inlineFragment (some typeCondition) _directives subselections =>
          let normalizedRest := normalizeSelectionSet schema parentType rest
          if schema.typesOverlapBool parentType typeCondition then
            normalizeSelectionSet schema parentType (subselections ++ rest)
          else
            normalizedRest
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    first
    | exact Nat.lt_of_le_of_lt
        (size_withoutFieldsWithResponseName_le schema responseName rest)
        (by
          simp [SelectionSet.size, Selection.size]
          omega)
    | (have hmerge :=
        size_mergeSelectionSets_validFieldsWithResponseName_le
          schema parentType responseName rest
       simp [selectionSet_size_append, SelectionSet.size,
         Selection.size]
       omega)
    | (simp [SelectionSet.size, Selection.size]
       omega)
    | (rw [selectionSet_size_append subselections rest]
       simp [SelectionSet.size, Selection.size]
       try omega)

-- Ground-type normalization of an operation
def normalizeOperation (schema : Schema)
    (operation : Operation) : Operation :=
  { operation with
    selectionSet :=
      normalizeSelectionSet schema operation.rootType operation.selectionSet }

-----------------------------------------------------------------------------------------
-- Ground Type Normalization Semantics Preservation
-----------------------------------------------------------------------------------------

mutual
  -- Proof-facing predicate for directive-free ground normalization: every modeled
  -- directive list in a selection is empty.
  def selectionDirectiveFree : Selection -> Prop
    | .field _responseName _fieldName _arguments directives selectionSet =>
        directives = [] ∧ selectionSetDirectiveFree selectionSet
    | .inlineFragment _typeCondition directives selectionSet =>
        directives = [] ∧ selectionSetDirectiveFree selectionSet

  -- Structural list form, chosen so hypotheses reduce directly on selection sets.
  def selectionSetDirectiveFree : List Selection -> Prop
    | [] => True
    | selection :: rest =>
        selectionDirectiveFree selection ∧ selectionSetDirectiveFree rest
end

-- Operation-level wrapper for the directive-free source-operation assumption.
def operationDirectiveFree (operation : Operation) : Prop :=
  selectionSetDirectiveFree operation.selectionSet

def operationsEquivalent (schema : Schema)
    (left right : Operation) : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    variableValues fuel (source : Execution.ResolverValue ObjectRef),
    Execution.executeQueryWithFuel schema resolvers variableValues left fuel source
      =
    Execution.executeQueryWithFuel schema resolvers variableValues right fuel source

-- Final resolver-parametric correctness statement for the ground-type normalizer.
-- Operation-level proof wrappers live in
-- `GraphQL.NormalForm.GroundTypeNormalization.OperationSemantics`.
def groundTypeNormalFormSemanticsPreservation (schema : Schema)
    (operation : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      operationDirectiveFree operation ->
        operationsEquivalent schema operation (normalizeOperation schema operation)

-----------------------------------------------------------------------------------------
-- Ground Type Normal Predicate
-----------------------------------------------------------------------------------------

-- Spec-inspired normal-form invariant: non-spec predicate requiring a flat field-only
-- selection layer.
def selectionsAllFields (selectionSet : List Selection) : Prop :=
  ∀ selection, selection ∈ selectionSet -> Selection.isField selection

-- Spec-inspired normal-form invariant: non-spec predicate requiring a flat
-- inline-fragment-only selection layer.
def selectionsAllInlineFragments (selectionSet : List Selection) : Prop :=
  ∀ selection, selection ∈ selectionSet ->
    Selection.isInlineFragment selection

-- Spec-inspired `GetPossibleTypes` grounding: non-spec predicate for object-grounded
-- selections.
mutual
  def selectionGroundTyped (schema : Schema) : Selection -> Prop
    | .field _responseName _fieldName _arguments _directives selectionSet =>
        (selectionsAllFields selectionSet ∨ selectionsAllInlineFragments selectionSet)
          ∧ selectionSetGroundTyped schema selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        schema.objectType typeCondition
          ∧ selectionsAllFields selectionSet
          ∧ selectionSetGroundTyped schema selectionSet
    | .inlineFragment none _directives selectionSet =>
        selectionsAllFields selectionSet
          ∧ selectionSetGroundTyped schema selectionSet

  def selectionSetGroundTyped (schema : Schema)
      (selectionSet : List Selection) : Prop :=
    (selectionsAllFields selectionSet ∨ selectionsAllInlineFragments selectionSet)
      ∧ ∀ selection, selection ∈ selectionSet -> selectionGroundTyped schema selection
end

-- Spec-inspired non-redundancy helper: response names are unique at one
-- selection-set layer.
def responseNamesNodup (selectionSet : List Selection) : Prop :=
  (selectionSet.filterMap Selection.responseName?).Nodup

-- Spec-inspired fragment grounding invariant: non-spec uniqueness predicate for
-- inline-fragment type conditions.
def inlineFragmentTypeConditionsNodup
    (selectionSet : List Selection) : Prop :=
  (selectionSet.filterMap (fun selection =>
    match selection with
    | .inlineFragment (some typeCondition) _directives _selectionSet =>
        some typeCondition
    | _ => none)).Nodup

-- Spec-inspired non-redundancy: non-spec predicate used by this project's normal form
-- rather than by GraphQL itself.
mutual
  def selectionNonRedundant : Selection -> Prop
    | .field _responseName _fieldName _arguments _directives selectionSet =>
        selectionSetNonRedundant selectionSet
    | .inlineFragment _typeCondition _directives selectionSet =>
        selectionSetNonRedundant selectionSet

  def selectionSetNonRedundant (selectionSet : List Selection) : Prop :=
    responseNamesNodup selectionSet
      ∧ inlineFragmentTypeConditionsNodup selectionSet
      ∧ ∀ selection, selection ∈ selectionSet -> selectionNonRedundant selection
end

-- Spec-inspired normal-form invariant: combines object grounding with this project's
-- response-name/type-condition non-redundancy predicate.
def selectionSetNormal (schema : Schema)
    (selectionSet : List Selection) : Prop :=
  selectionSetGroundTyped schema selectionSet ∧ selectionSetNonRedundant selectionSet

-- Spec-inspired operation normality: non-spec wrapper over the root selection set.
def operationNormal (schema : Schema)
    (operation : Operation) : Prop :=
  selectionSetNormal schema operation.selectionSet

-- Public normality statement for the ground-type normalizer. The theorem witness is
-- `GraphQL.NormalForm.GroundTypeNormalization.normalizeOperation_normal`.
def normalizeOperationNormal (schema : Schema)
    (operation : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema ->
    operationNormal schema (normalizeOperation schema operation)

-----------------------------------------------------------------------------------------
-- Ground Type Normalization Validity
-----------------------------------------------------------------------------------------

-- Type-condition feasibility for one field occurrence: the inline-fragment type
-- conditions between the field and its nearest parent field/root selection set,
-- including that parent type itself, have a nonempty possible-object intersection.
def typeConditionStackFeasible (schema : Schema) (typeConditions : List Name) :
    Prop :=
  ∃ objectType,
    ∀ typeCondition, typeCondition ∈ typeConditions ->
      objectType ∈ schema.getPossibleTypes typeCondition

mutual
  -- Existential helper: this selection may expose a field whose accumulated
  -- type-condition stack is feasible.
  def selectionContainsTypeConditionFeasibleField (schema : Schema)
      (typeConditions : List Name) : Selection -> Prop
    | .field _responseName _fieldName _arguments _directives _selectionSet =>
        typeConditionStackFeasible schema typeConditions
    | .inlineFragment none _directives selectionSet =>
        selectionSetContainsTypeConditionFeasibleField schema typeConditions
          selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        selectionSetContainsTypeConditionFeasibleField schema
          (typeCondition :: typeConditions) selectionSet

  def selectionSetContainsTypeConditionFeasibleField (schema : Schema)
      (typeConditions : List Name) (selectionSet : List Selection) : Prop :=
    match selectionSet with
    | [] => False
    | selection :: rest =>
        selectionContainsTypeConditionFeasibleField schema typeConditions
          selection
          ∨ selectionSetContainsTypeConditionFeasibleField schema
            typeConditions rest
end

mutual
  -- Recursive source-operation assumption for validity preservation: every nonempty
  -- selection set has at least one field whose inline-fragment type-condition stack is
  -- feasible, and the same property holds for nested nonempty field selection sets.
  def selectionTypeConditionFeasible (schema : Schema)
      (parentType : Name) (typeConditions : List Name) : Selection -> Prop
    | .field _responseName fieldName _arguments _directives selectionSet =>
        match selectionSet with
        | [] => True
        | _ :: _ =>
            match schema.lookupField parentType fieldName with
            | some fieldDefinition =>
                selectionSetContainsTypeConditionFeasibleField schema
                  [fieldDefinition.outputType.namedType] selectionSet
                  ∧ selectionsTypeConditionFeasible schema
                    fieldDefinition.outputType.namedType
                    [fieldDefinition.outputType.namedType] selectionSet
            | none => False
    | .inlineFragment none _directives selectionSet =>
        selectionsTypeConditionFeasible schema parentType
          typeConditions selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        selectionsTypeConditionFeasible schema parentType
          (typeCondition :: typeConditions) selectionSet

  def selectionsTypeConditionFeasible (schema : Schema)
      (parentType : Name) (typeConditions : List Name)
      (selectionSet : List Selection) : Prop :=
    match selectionSet with
    | [] => True
    | selection :: rest =>
        selectionTypeConditionFeasible schema parentType typeConditions selection
          ∧ selectionsTypeConditionFeasible schema parentType typeConditions rest
end

def selectionSetTypeConditionFeasible (schema : Schema)
    (parentType : Name) (typeConditions : List Name)
    (selectionSet : List Selection) : Prop :=
  selectionSetContainsTypeConditionFeasibleField schema typeConditions
    selectionSet
    ∧ selectionsTypeConditionFeasible schema parentType typeConditions
      selectionSet

-- Strong proof-facing form used by validity preservation: whenever the normalizer is
-- asked to process a nonempty selection set in a concrete scope, that selection set has a
-- feasible field in that scope. This is intentionally stronger than the operation-level
-- wrapper above; later proofs can try to derive it from source-operation reachability.
def selectionSetsTypeConditionFeasibleInEveryScope (schema : Schema) : Prop :=
  ∀ parentType selectionSet,
    selectionSet ≠ [] ->
      selectionSetTypeConditionFeasible schema parentType [parentType]
        selectionSet

-- Public validity-preservation statement for the ground-type normalizer.
def normalizeOperationValid (schema : Schema)
    (operation : Operation) : Prop :=
      SchemaWellFormedness.schemaWellFormed schema ->
      Validation.operationDefinitionValid schema operation ->
      operationDirectiveFree operation ->
        selectionSetsTypeConditionFeasibleInEveryScope schema ->
          Validation.operationDefinitionValid schema
            (normalizeOperation schema operation)

-----------------------------------------------------------------------------------------
-- Ground Type Lifting
-----------------------------------------------------------------------------------------

/-!
Ground lifting currently exposes the alternative lifting transform only. The theorem
modules cover directive-freeness and response-name-free preservation, append/field-filter
structural facts, scoped selection helpers, and an operation-level semantic wrapper once
selection-set preservation is supplied. There is no public top-level lifting-normal
predicate yet.
-/

def leafTypeNameBool (schema : Schema) (typeName : Name) : Bool :=
  match schema.lookupType typeName with
  | some (.builtinScalar _) => true
  | some (.customScalar _) => true
  | some (.enum _) => true
  | _ => false

-- Returns the object branches that can execute for an already-unwrapped composite return
-- type.
def groundObjectTypesForType (schema : Schema) (returnType : Name) :
    List Name :=
  if objectTypeNameBool schema returnType then
    [returnType]
  else
    schema.getPossibleTypes returnType

mutual
  -- Candidate two-phase normalizer phase 1: duplicate each composite field's
  -- original child selection set under every ground runtime object branch.
  def groundLiftSelection (schema : Schema) (parentType : Name) :
      Selection -> Selection
    | .field responseName fieldName arguments directives selectionSet =>
        match schema.lookupField parentType fieldName with
        | none =>
            .field responseName fieldName arguments directives
              (groundLiftSelectionSet schema parentType selectionSet)
        | some fieldDefinition =>
            let returnType := fieldDefinition.outputType.namedType
            let liftedSelectionSet :=
              if leafTypeNameBool schema returnType then
                []
              else if objectTypeNameBool schema returnType then
                groundLiftSelectionSet schema returnType selectionSet
              else
                (groundObjectTypesForType schema returnType).map
                  (fun objectType =>
                    .inlineFragment (some objectType) []
                      (groundLiftSelectionSet schema objectType selectionSet))
            .field responseName fieldName arguments directives liftedSelectionSet
    | .inlineFragment none directives selectionSet =>
        .inlineFragment none directives
          (groundLiftSelectionSet schema parentType selectionSet)
    | .inlineFragment (some typeCondition) directives selectionSet =>
        .inlineFragment (some typeCondition) directives
          (groundLiftSelectionSet schema typeCondition selectionSet)

  def groundLiftSelectionSet (schema : Schema) (parentType : Name) :
      List Selection -> List Selection
    | [] => []
    | selection :: rest =>
        groundLiftSelection schema parentType selection
          :: groundLiftSelectionSet schema parentType rest
end

def groundLiftOperation (schema : Schema) (operation : Operation) :
    Operation :=
  { operation with
    selectionSet := groundLiftSelectionSet schema operation.rootType
      operation.selectionSet }

-----------------------------------------------------------------------------------------
-- Complete Normalization
-----------------------------------------------------------------------------------------

namespace CompleteNormalization

abbrev BoolVar := Name
abbrev BoolCase := List (BoolVar × Bool)

mutual
  def inputValueBooleanVariables : InputValue -> List BoolVar
    | .variable name => [name]
    | .list values => inputValuesBooleanVariables values
    | .object fields => inputObjectFieldsBooleanVariables fields
    | _ => []

  def inputValuesBooleanVariables : List InputValue -> List BoolVar
    | [] => []
    | value :: rest =>
        inputValueBooleanVariables value ++ inputValuesBooleanVariables rest

  def inputObjectFieldsBooleanVariables :
      List (Name × InputValue) -> List BoolVar
    | [] => []
    | (_name, value) :: rest =>
        inputValueBooleanVariables value
          ++ inputObjectFieldsBooleanVariables rest
end

def directiveBooleanVariables : DirectiveApplication -> List BoolVar
  | .skip ifArgument => inputValueBooleanVariables ifArgument
  | .include ifArgument => inputValueBooleanVariables ifArgument

def directivesBooleanVariables :
    List DirectiveApplication -> List BoolVar
  | [] => []
  | directive :: rest =>
      directiveBooleanVariables directive ++ directivesBooleanVariables rest

mutual
  def selectionBooleanVariables : Selection -> List BoolVar
    | .field _responseName _fieldName _arguments directives selectionSet =>
        directivesBooleanVariables directives
          ++ selectionSetBooleanVariables selectionSet
    | .inlineFragment _typeCondition directives selectionSet =>
        directivesBooleanVariables directives
          ++ selectionSetBooleanVariables selectionSet

  def selectionSetBooleanVariables : List Selection -> List BoolVar
    | [] => []
    | selection :: rest =>
        selectionBooleanVariables selection ++ selectionSetBooleanVariables rest
end

def boolVariableMem (varName : BoolVar) :
    List BoolVar -> Bool
  | [] => false
  | candidate :: rest =>
      if candidate == varName then true else boolVariableMem varName rest

def dedupBoolVars : List BoolVar -> List BoolVar
  | [] => []
  | varName :: rest =>
      let dedupedRest := dedupBoolVars rest
      if boolVariableMem varName dedupedRest then
        dedupedRest
      else
        varName :: dedupedRest

def allBoolCases : List BoolVar -> List BoolCase
  | [] => [[]]
  | varName :: rest =>
      let restCases := allBoolCases rest
      restCases.map (fun boolCase => (varName, false) :: boolCase)
        ++ restCases.map
          (fun boolCase => (varName, true) :: boolCase)

def BoolCase.lookup? (boolCase : BoolCase)
    (varName : BoolVar) : Option Bool :=
  match boolCase with
  | [] => none
  | (candidate, value) :: rest =>
      if candidate == varName then some value else BoolCase.lookup? rest varName

def inputValueBoolIn?
    (boolCase : BoolCase) : InputValue -> Option Bool
  | .variable varName => BoolCase.lookup? boolCase varName
  | value => value.staticBoolean?

def directiveAllowsIn
    (boolCase : BoolCase) : DirectiveApplication -> Bool
  | .skip ifArgument =>
      match inputValueBoolIn? boolCase ifArgument with
      | some value => !value
      | none => false
  | .include ifArgument =>
      match inputValueBoolIn? boolCase ifArgument with
      | some value => value
      | none => false

def directivesAllowIn
    (boolCase : BoolCase)
    (directives : List DirectiveApplication) : Bool :=
  directives.all (fun directive =>
    directiveAllowsIn boolCase directive)

def directiveForBit
    (varName : BoolVar) (value : Bool) : DirectiveApplication :=
  if value then
    .include (.variable varName)
  else
    .skip (.variable varName)

def wrapWithBoolCase
    (boolCase : BoolCase) :
    List Selection -> List Selection
  | selectionSet =>
      match boolCase with
      | [] => selectionSet
      | (varName, value) :: rest =>
          [ .inlineFragment none [directiveForBit varName value]
              (wrapWithBoolCase rest selectionSet) ]

section FilterSelectionSetBoolCaseTermination

/-! Private termination support for `filterSelectionSetBoolCase`. -/

private theorem selection_size_pos (selection : Selection) :
    0 < selection.size := by
  cases selection <;> simp [Selection.size] <;> omega

private theorem selectionSet_size_tail_lt_cons
    (selection : Selection) (rest : List Selection) :
    SelectionSet.size rest < SelectionSet.size (selection :: rest) := by
  simp [SelectionSet.size]
  exact Nat.lt_add_of_pos_left (selection_size_pos selection)

private theorem selectionSet_size_child_lt_cons_field
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection) :
    SelectionSet.size selectionSet <
      SelectionSet.size
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) := by
  simp [SelectionSet.size, Selection.size]
  omega

private theorem selectionSet_size_child_lt_cons_inline
    (typeCondition : Option Name) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection) :
    SelectionSet.size selectionSet <
      SelectionSet.size
        (Selection.inlineFragment typeCondition directives selectionSet
          :: rest) := by
  simp [SelectionSet.size, Selection.size]
  omega

end FilterSelectionSetBoolCaseTermination

def filterSelectionSetBoolCase
    (boolCase : BoolCase) :
    List Selection -> List Selection
  | [] => []
  | selection :: rest =>
      let collectedRest :=
        filterSelectionSetBoolCase boolCase rest
      match selection with
      | .field responseName fieldName arguments directives selectionSet =>
          if directivesAllowIn boolCase directives then
            let filteredSelectionSet :=
              filterSelectionSetBoolCase boolCase selectionSet
            match selectionSet, filteredSelectionSet with
            | [], _ =>
                .field responseName fieldName arguments [] [] :: collectedRest
            | _ :: _, [] =>
                .field responseName fieldName arguments [] [] :: collectedRest
            | _ :: _, child :: children =>
                .field responseName fieldName arguments [] (child :: children)
                  :: collectedRest
          else
            collectedRest
      | .inlineFragment typeCondition directives selectionSet =>
          if directivesAllowIn boolCase directives then
            match filterSelectionSetBoolCase boolCase selectionSet with
            | [] => collectedRest
            | child :: children =>
                .inlineFragment typeCondition [] (child :: children)
                  :: collectedRest
          else
            collectedRest
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    first
    | exact selectionSet_size_tail_lt_cons selection rest
    | exact selectionSet_size_child_lt_cons_field responseName fieldName
        arguments directives selectionSet rest
    | exact selectionSet_size_child_lt_cons_inline typeCondition
        directives selectionSet rest

def normalizeBoolCaseForType
    (schema : Schema) (boolCase : BoolCase) (returnType : Name)
    (selectionSet : List Selection) : List Selection :=
  normalizeSelectionSet schema returnType
    (filterSelectionSetBoolCase boolCase selectionSet)

def completeNormalizeRootSelectionSet
    (schema : Schema) (variables : List BoolVar)
    (parentType : Name) (selectionSet : List Selection) :
    List Selection :=
  List.flatten ((allBoolCases variables).map
    (fun boolCase =>
      match normalizeSelectionSet schema parentType
          (filterSelectionSetBoolCase boolCase selectionSet) with
      | [] => []
      | selection :: rest =>
          wrapWithBoolCase boolCase (selection :: rest)))

-- Named operation-global variable policy used by CompleteNormalization predicates.
def operationBoolVars (operation : Operation) :
    List BoolVar :=
  dedupBoolVars (selectionSetBooleanVariables operation.selectionSet)

def completeNormalizeOperation
    (schema : Schema) (operation : Operation) : Operation :=
  let variables := operationBoolVars operation
  { operation with
    selectionSet :=
      completeNormalizeRootSelectionSet schema variables operation.rootType
        operation.selectionSet }

end CompleteNormalization

export CompleteNormalization
  (BoolVar BoolCase inputValueBooleanVariables
    inputValuesBooleanVariables inputObjectFieldsBooleanVariables
    directiveBooleanVariables directivesBooleanVariables
    selectionBooleanVariables selectionSetBooleanVariables boolVariableMem
    dedupBoolVars allBoolCases BoolCase.lookup?
    inputValueBoolIn? directiveAllowsIn
    directivesAllowIn directiveForBit
    wrapWithBoolCase
    filterSelectionSetBoolCase normalizeBoolCaseForType
    completeNormalizeRootSelectionSet
    completeNormalizeOperation operationBoolVars)

-----------------------------------------------------------------------------------------
-- Complete Normalization Semantics Preservation
-----------------------------------------------------------------------------------------

def operationBoolVarsComplete
    (operation : Operation) (variableValues : Execution.VariableValues) : Prop :=
  ∀ varName, varName ∈ operationBoolVars operation ->
    ∃ value,
      Execution.inputValueBoolean? variableValues (.variable varName) =
        some value

def completeNormalizationSemanticsPreserved
    (schema : Schema) (operation : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
        variableValues fuel (source : Execution.ResolverValue ObjectRef),
        operationBoolVarsComplete operation variableValues ->
          Execution.executeQueryWithFuel schema resolvers variableValues operation
            fuel source
            =
          Execution.executeQueryWithFuel schema resolvers variableValues
            (completeNormalizeOperation schema operation) fuel source

-----------------------------------------------------------------------------------------
-- Complete Normal Predicate And Normalization Statement
-----------------------------------------------------------------------------------------

namespace CompleteNormalization

-- Complete Boolean minterm: every operation Boolean variable appears exactly once.
-- The order in the `BoolCase` is intentionally irrelevant to the variable list order.
def completeNormalBoolCase
    (variables : List BoolVar) (boolCase : BoolCase) : Prop :=
  variables.Nodup
    ∧ (boolCase.map Prod.fst).Nodup
    ∧ ∀ varName,
      varName ∈ boolCase.map Prod.fst ↔ varName ∈ variables

-- Boolean conditions are compared extensionally, so different stem orders can denote
-- the same minterm.
def completeNormalBoolCasesEquivalent (left right : BoolCase) : Prop :=
  ∀ varName value,
    (varName, value) ∈ left ↔ (varName, value) ∈ right

-- A Boolean case stem is a chain of anonymous inline fragments, one singleton
-- skip/include directive per variable, ending in the branch body.
def completeNormalBooleanStem :
    BoolCase -> Selection -> List Selection -> Prop
  | [], _selection, _body => False
  | [(varName, value)],
      .inlineFragment none [directive] body, branchBody =>
        directive = directiveForBit varName value
          ∧ body = branchBody
  | (varName, value) :: rest,
      .inlineFragment none [directive] [child], branchBody =>
        directive = directiveForBit varName value
          ∧ completeNormalBooleanStem rest child branchBody
  | _, _, _ => False

-- Complete DNF over Boolean directive variables for the nonempty cases. Branch
-- order is irrelevant; stem variable order is irrelevant; empty cases are omitted;
-- repeated branch selections are rejected.
def completeNormalSelectionSet
    (schema : Schema) (variables : List BoolVar)
    (selectionSet : List Selection) : Prop :=
  variables.Nodup
    ∧ match variables with
      | [] => selectionSetNormal schema selectionSet
          ∧ selectionSetDirectiveFree selectionSet
      | _ :: _ =>
          selectionSet.Nodup
          ∧ (∀ selection, selection ∈ selectionSet ->
            ∃ boolCase body,
              completeNormalBoolCase variables boolCase
                ∧ completeNormalBooleanStem boolCase selection body
                ∧ selectionSetNormal schema body
                ∧ selectionSetDirectiveFree body)
          ∧ (∀ left right leftCase rightCase leftBody rightBody,
            left ∈ selectionSet ->
            right ∈ selectionSet ->
            completeNormalBoolCase variables leftCase ->
            completeNormalBoolCase variables rightCase ->
            completeNormalBooleanStem leftCase left leftBody ->
            completeNormalBooleanStem rightCase right rightBody ->
            selectionSetDirectiveFree leftBody ->
            selectionSetDirectiveFree rightBody ->
            completeNormalBoolCasesEquivalent leftCase rightCase ->
              left = right)

def completeNormalOperation
    (schema : Schema) (operation : Operation) : Prop :=
  completeNormalSelectionSet schema
    (operationBoolVars operation) operation.selectionSet

end CompleteNormalization

export CompleteNormalization
  (completeNormalBoolCase completeNormalBoolCasesEquivalent
    completeNormalBooleanStem completeNormalSelectionSet completeNormalOperation)

def completeNormalizeOperationNormal
    (schema : Schema) (operation : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      completeNormalOperation schema
        (completeNormalizeOperation schema operation)

-----------------------------------------------------------------------------------------
-- Complete Normalization Validity
-----------------------------------------------------------------------------------------

namespace CompleteNormalization

mutual
  def selectionContributesInBoolCase
      (boolCase : BoolCase) : Selection -> Prop
    | .field _responseName _fieldName _arguments directives _selectionSet =>
        directivesAllowIn boolCase directives = true
    | .inlineFragment _typeCondition directives selectionSet =>
        directivesAllowIn boolCase directives = true
          ∧ selectionSetContributesInBoolCase boolCase selectionSet

  def selectionSetContributesInBoolCase
      (boolCase : BoolCase) : List Selection -> Prop
    | [] => False
    | selection :: rest =>
        selectionContributesInBoolCase boolCase selection
          ∨ selectionSetContributesInBoolCase boolCase rest
end

mutual
  def selectionBoolCaseCompositeChildrenSurvive
      (boolCase : BoolCase) : Selection -> Prop
    | .field _responseName _fieldName _arguments directives selectionSet =>
        directivesAllowIn boolCase directives = true ->
          match selectionSet with
          | [] => True
          | _ :: _ =>
              selectionSetContributesInBoolCase boolCase selectionSet
                ∧ selectionSetBoolCaseCompositeChildrenSurvive boolCase
                  selectionSet
    | .inlineFragment _typeCondition directives selectionSet =>
        directivesAllowIn boolCase directives = true ->
          selectionSetBoolCaseCompositeChildrenSurvive boolCase selectionSet

  def selectionSetBoolCaseCompositeChildrenSurvive
      (boolCase : BoolCase) : List Selection -> Prop
    | [] => True
    | selection :: rest =>
        selectionBoolCaseCompositeChildrenSurvive boolCase selection
          ∧ selectionSetBoolCaseCompositeChildrenSurvive boolCase rest
end

def completeBoolCasesCompositeChildrenSurvive
    (operation : Operation) : Prop :=
  ∀ boolCase, boolCase ∈ allBoolCases (operationBoolVars operation) ->
    selectionSetBoolCaseCompositeChildrenSurvive boolCase
      operation.selectionSet

end CompleteNormalization

export CompleteNormalization
  (completeBoolCasesCompositeChildrenSurvive)

def completeNormalizeOperationValid
    (schema : Schema) (operation : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    selectionSetsTypeConditionFeasibleInEveryScope schema ->
    completeBoolCasesCompositeChildrenSurvive operation ->
      Validation.operationDefinitionValid schema
        (completeNormalizeOperation schema operation)

end NormalForm

end GraphQL
