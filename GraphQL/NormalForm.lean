import GraphQL.DataModel
import GraphQL.SchemaWellFormedness

/-! GraphQL operation normal form

This project-specific normal form merges same-response-name field selections and grounds
abstract returns through possible object types. The public semantic-preservation predicates
in this module are proved by
`GraphQL.NormalForm.GroundTypeNormalization.groundTypeNormalFormSemanticsPreservation` and
`GraphQL.NormalForm.GroundTypeNormalization.groundNormalFormCorrect`.
-/
namespace GraphQL

namespace NormalForm

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

mutual
  -- Helper predicate: one selection cannot contribute a field with the given response
  -- name in the current type scope.
  def selectionResponseNameFree (schema : Schema)
      (parentType responseName : Name) : Selection -> Prop
    | .field selectionResponseName _fieldName _arguments _directives _selectionSet =>
        selectionResponseName ≠ responseName
    | .inlineFragment none _directives selectionSet =>
        selectionSetResponseNameFree schema parentType responseName selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        schema.typesOverlapBool parentType typeCondition = true ->
          selectionSetResponseNameFree schema parentType responseName selectionSet

  def selectionSetResponseNameFree (schema : Schema)
      (parentType responseName : Name)
      (selectionSet : List Selection) : Prop :=
    ∀ selection, selection ∈ selectionSet ->
      selectionResponseNameFree schema parentType responseName selection
end

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

-- Spec 5.3.2 field merging / 6.3.2 subfield collection: partial normalizer; merges
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
                  (schema.getPossibleTypes returnType).map
                    (fun objectType =>
                      .inlineFragment (some objectType) []
                        (normalizeSelectionSet schema objectType mergedSubselections))
              .field responseName fieldName arguments directives normalizedSubselections
                :: normalizedRest
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

-- Public GraphCoQL-style grounding helper: object return types normalize directly; abstract
-- interface/union return types specialize into one object fragment per possible type.
def normalizeMergedSelectionSetForType
    (schema : Schema) (returnType : Name)
    (selectionSet : List Selection) : List Selection :=
  if objectTypeNameBool schema returnType then
    normalizeSelectionSet schema returnType selectionSet
  else
    (schema.getPossibleTypes returnType).map
      (fun objectType =>
        .inlineFragment (some objectType) []
          (normalizeSelectionSet schema objectType selectionSet))

-- Spec-inspired operation normalizer: non-spec wrapper around selection-set normalization.
def normalizeOperation (schema : Schema)
    (operation : Operation) : Operation :=
  { operation with
    selectionSet := normalizeSelectionSet schema operation.rootType
      operation.selectionSet }

def operationsEquivalent (schema : Schema)
    (left right : Operation) : Prop :=
  ∀ (ObjectIdentity : Type) (resolvers : Execution.Resolvers ObjectIdentity)
    variableValues depth (source : Execution.Value ObjectIdentity),
    Execution.executeQueryAtDepth schema resolvers variableValues left depth source
      =
    Execution.executeQueryAtDepth schema resolvers variableValues right depth source

def groundTypeNormalFormSemanticsPreserved (schema : Schema)
    (operation : Operation) : Prop :=
  operationsEquivalent schema operation
    (normalizeOperation schema operation)

-- Store-backed correctness statement for the ground-type normalizer. The theorem witness is
-- `GraphQL.NormalForm.GroundTypeNormalization.groundNormalFormCorrect`.
def groundNormalFormCorrect (schema : Schema)
    (operation : Operation) : Prop :=
  DataModel.operationsEquivalentOnData schema operation
    (normalizeOperation schema operation)

-- Final resolver-parametric correctness statement for the ground-type normalizer. The theorem
-- witness is
-- `GraphQL.NormalForm.GroundTypeNormalization.groundTypeNormalFormSemanticsPreservation`.
def groundTypeNormalFormSemanticsPreservation (schema : Schema)
    (operation : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      operationDirectiveFree operation ->
        groundTypeNormalFormSemanticsPreserved schema operation

end NormalForm

end GraphQL
