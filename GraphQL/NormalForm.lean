import GraphQL.Execution

/-!
Spec reference: GraphQL September 2025.
- 5.3.2 Field Selection Merging and 6.3.2 Field Collection: normalization merges
  same-response-name field subselections in the spirit of GraphQL's merge/collect
  behavior.
- 5.5.2.3 Fragment Spread Is Possible and `GetPossibleTypes`: abstract type conditions are
  grounded through possible object types.
- Fidelity note: GraphQL does not define this normal form. This is a project-specific
  canonicalization scaffold; it is partial and does not yet prove semantic preservation.
-/
namespace GraphQL

namespace NormalForm

-- Spec-inspired normal-form invariant: non-spec predicate requiring a flat field-only
-- selection layer.
def selectionsAllFields (selectionSet : List Semantic.Selection) : Prop :=
  ∀ selection, selection ∈ selectionSet -> Semantic.Selection.isField selection

-- Spec-inspired normal-form invariant: non-spec predicate requiring a flat
-- inline-fragment-only selection layer.
def selectionsAllInlineFragments (selectionSet : List Semantic.Selection) : Prop :=
  ∀ selection, selection ∈ selectionSet ->
    Semantic.Selection.isInlineFragment selection

-- Spec-inspired `GetPossibleTypes` grounding: non-spec predicate for object-grounded
-- semantic selections.
mutual
  def selectionGroundTyped (schema : Schema) : Semantic.Selection -> Prop
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
      (selectionSet : List Semantic.Selection) : Prop :=
    (selectionsAllFields selectionSet ∨ selectionsAllInlineFragments selectionSet)
      ∧ ∀ selection, selection ∈ selectionSet -> selectionGroundTyped schema selection
end

-- Spec-inspired non-redundancy helper: response names are unique at one semantic
-- selection-set layer.
def responseNamesNodup (selectionSet : List Semantic.Selection) : Prop :=
  (selectionSet.filterMap Semantic.Selection.responseName?).Nodup

-- Spec-inspired fragment grounding invariant: non-spec uniqueness predicate for
-- inline-fragment type conditions.
def inlineFragmentTypeConditionsNodup
    (selectionSet : List Semantic.Selection) : Prop :=
  (selectionSet.filterMap (fun selection =>
    match selection with
    | .inlineFragment (some typeCondition) _directives _selectionSet =>
        some typeCondition
    | _ => none)).Nodup

-- Spec-inspired non-redundancy: non-spec predicate used by this project's normal form
-- rather than by GraphQL itself.
mutual
  def selectionNonRedundant : Semantic.Selection -> Prop
    | .field _responseName _fieldName _arguments _directives selectionSet =>
        selectionSetNonRedundant selectionSet
    | .inlineFragment _typeCondition _directives selectionSet =>
        selectionSetNonRedundant selectionSet

  def selectionSetNonRedundant (selectionSet : List Semantic.Selection) : Prop :=
    responseNamesNodup selectionSet
      ∧ inlineFragmentTypeConditionsNodup selectionSet
      ∧ ∀ selection, selection ∈ selectionSet -> selectionNonRedundant selection
end

-- Spec-inspired normal-form invariant: combines object grounding with this project's
-- response-name/type-condition non-redundancy predicate.
def selectionSetNormal (schema : Schema)
    (selectionSet : List Semantic.Selection) : Prop :=
  selectionSetGroundTyped schema selectionSet ∧ selectionSetNonRedundant selectionSet

-- Spec-inspired semantic operation normality: non-spec wrapper over the root selection
-- set.
def semanticOperationNormal (schema : Schema)
    (operation : Semantic.Operation) : Prop :=
  selectionSetNormal schema operation.selectionSet

-- Spec-inspired operation normality after fragment inlining.
def operationNormal (schema : Schema) (operation : GraphQL.Operation) : Prop :=
  semanticOperationNormal schema (Semantic.fromOperation operation)

-- Spec 5.5.2.3 `GetPossibleTypes` helper for deciding whether an already-unwrapped
-- named return type can be normalized directly, or must be grounded through object cases.
def objectTypeNameBool (schema : Schema) (typeName : Name) : Bool :=
  match schema.lookupType typeName with
  | some (.object _) => true
  | _ => false

-- Spec 6.3.2 `CollectSubfields` analogue over semantic selections, written
-- structurally so termination and size reasoning can reduce it directly.
def mergeSelectionSets : List Semantic.Selection -> List Semantic.Selection
  | [] => []
  | selection :: rest => selection.subselections ++ mergeSelectionSets rest

private theorem selectionSet_size_append (left right : List Semantic.Selection) :
    Semantic.SelectionSet.size (left ++ right)
      = Semantic.SelectionSet.size left + Semantic.SelectionSet.size right := by
  induction left with
  | nil => simp [Semantic.SelectionSet.size]
  | cons selection rest ih =>
      simp [Semantic.SelectionSet.size, ih, Nat.add_assoc]

private theorem mergeSelectionSets_append
    (left right : List Semantic.Selection) :
    mergeSelectionSets (left ++ right)
      = mergeSelectionSets left ++ mergeSelectionSets right := by
  induction left with
  | nil => simp [mergeSelectionSets]
  | cons selection rest ih =>
      simp [mergeSelectionSets, ih, List.append_assoc]

mutual
  -- Spec 6.3.2 field collection helper: finds fields with one response name, descending
  -- through fragments that can contribute selections in the current type scope.
  def validFieldsWithResponseName (schema : Schema)
      (parentType responseName : Name) :
      List Semantic.Selection -> List Semantic.Selection
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
      List Semantic.Selection -> List Semantic.Selection
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
      Semantic.SelectionSet.size
          (withoutFieldsWithResponseName schema responseName selectionSet)
        ≤ Semantic.SelectionSet.size selectionSet
  | [] => by
      simp [withoutFieldsWithResponseName, Semantic.SelectionSet.size]
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hrest :=
            size_withoutFieldsWithResponseName_le schema responseName rest
          by_cases h : (fieldResponseName == responseName) = true
          · simp [withoutFieldsWithResponseName, h, Semantic.SelectionSet.size,
              Semantic.Selection.size]
            omega
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldsWithResponseName, hfalse, Semantic.SelectionSet.size,
              Semantic.Selection.size]
            omega
      | inlineFragment typeCondition directives selectionSet =>
          have hselectionSet :=
            size_withoutFieldsWithResponseName_le schema responseName selectionSet
          have hrest :=
            size_withoutFieldsWithResponseName_le schema responseName rest
          cases typeCondition <;>
            simp [withoutFieldsWithResponseName, Semantic.SelectionSet.size,
              Semantic.Selection.size]
          all_goals omega
termination_by selectionSet => Semantic.SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [Semantic.SelectionSet.size, Semantic.Selection.size]
    omega

private theorem size_mergeSelectionSets_validFieldsWithResponseName_le
    (schema : Schema) (parentType responseName : Name) :
    ∀ selectionSet,
      Semantic.SelectionSet.size
          (mergeSelectionSets
            (validFieldsWithResponseName schema parentType responseName selectionSet))
        ≤ Semantic.SelectionSet.size selectionSet
  | [] => by
      simp [validFieldsWithResponseName, mergeSelectionSets,
        Semantic.SelectionSet.size]
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hrest :=
            size_mergeSelectionSets_validFieldsWithResponseName_le
              schema parentType responseName rest
          by_cases h : (fieldResponseName == responseName) = true
          · simp [validFieldsWithResponseName, mergeSelectionSets, h,
              selectionSet_size_append, Semantic.SelectionSet.size,
              Semantic.Selection.size, Semantic.Selection.subselections]
            omega
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [validFieldsWithResponseName, hfalse,
              Semantic.SelectionSet.size, Semantic.Selection.size]
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
                selectionSet_size_append, Semantic.SelectionSet.size,
                Semantic.Selection.size]
              omega
          | some typeCondition =>
              by_cases h : (schema.typesOverlapBool parentType typeCondition) = true
              · simp [validFieldsWithResponseName, h, mergeSelectionSets_append,
                  selectionSet_size_append, Semantic.SelectionSet.size,
                  Semantic.Selection.size]
                omega
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition = false := by
                  cases hmatch : schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [validFieldsWithResponseName, hfalse, Semantic.SelectionSet.size,
                  Semantic.Selection.size]
                omega
termination_by selectionSet => Semantic.SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [Semantic.SelectionSet.size, Semantic.Selection.size]
    omega

-- Spec 5.3.2 field merging / 6.3.2 subfield collection: partial normalizer; merges
-- same-response-name fields, recursively normalizes child selections, and grounds
-- abstract field return types through possible object types. This is terminating by
-- selection-set size.
def normalizeSelectionSet (schema : Schema) (parentType : Name) :
    List Semantic.Selection -> List Semantic.Selection
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
termination_by selectionSet => Semantic.SelectionSet.size selectionSet
decreasing_by
  all_goals
    first
    | exact Nat.lt_of_le_of_lt
        (size_withoutFieldsWithResponseName_le schema responseName rest)
        (by
          simp [Semantic.SelectionSet.size, Semantic.Selection.size]
          omega)
    | (have hmerge :=
        size_mergeSelectionSets_validFieldsWithResponseName_le
          schema parentType responseName rest
       simp [selectionSet_size_append, Semantic.SelectionSet.size,
         Semantic.Selection.size]
       omega)
    | (simp [Semantic.SelectionSet.size, Semantic.Selection.size]
       omega)
    | (rw [selectionSet_size_append subselections rest]
       simp [Semantic.SelectionSet.size, Semantic.Selection.size]
       try omega)

-- Public GraphCoQL-style grounding helper: object return types normalize directly; abstract
-- interface/union return types specialize into one object fragment per possible type.
def normalizeMergedSelectionSetForType
    (schema : Schema) (returnType : Name)
    (selectionSet : List Semantic.Selection) : List Semantic.Selection :=
  if objectTypeNameBool schema returnType then
    normalizeSelectionSet schema returnType selectionSet
  else
    (schema.getPossibleTypes returnType).map
      (fun objectType =>
        .inlineFragment (some objectType) []
          (normalizeSelectionSet schema objectType selectionSet))

-- Spec-inspired semantic normalizer: non-spec wrapper around selection-set
-- normalization.
def normalizeSemanticOperation (schema : Schema)
    (operation : Semantic.Operation) : Semantic.Operation :=
  { operation with
    selectionSet := normalizeSelectionSet schema operation.rootType
      operation.selectionSet }

theorem normalizeSemanticOperation_name (schema : Schema)
    (operation : Semantic.Operation) :
    (normalizeSemanticOperation schema operation).name = operation.name := by
  rfl

theorem normalizeSemanticOperation_rootType (schema : Schema)
    (operation : Semantic.Operation) :
    (normalizeSemanticOperation schema operation).rootType = operation.rootType := by
  rfl

theorem normalizeSemanticOperation_variableDefinitions (schema : Schema)
    (operation : Semantic.Operation) :
    (normalizeSemanticOperation schema operation).variableDefinitions
      = operation.variableDefinitions := by
  rfl

def semanticOperationsEquivalent (schema : Schema)
    (left right : Semantic.Operation) : Prop :=
  ∀ resolvers variableValues source,
    Execution.executeSemanticQuery schema resolvers variableValues left source
      =
    Execution.executeSemanticQuery schema resolvers variableValues right source

def groundTypeNormalFormSemanticsPreserved (schema : Schema)
    (operation : Semantic.Operation) : Prop :=
  semanticOperationsEquivalent schema operation
    (normalizeSemanticOperation schema operation)

-- Final correctness statement for the ground-type normalizer. This is intentionally
-- stated without proof in this definition-focused slice.
axiom groundTypeNormalFormSemanticsPreservation (schema : Schema)
    (operation : Semantic.Operation) :
  groundTypeNormalFormSemanticsPreserved schema operation

-- Spec-inspired operation normalization: non-spec transformation; currently clears named
-- fragments via `Semantic.fromOperation` and has only the fragment-empty theorem below.
def normalizeOperation (schema : Schema) (operation : GraphQL.Operation) :
    GraphQL.Operation :=
  (normalizeSemanticOperation schema (Semantic.fromOperation operation)).toOperation

theorem normalizeOperation_fragments_empty (schema : Schema)
    (operation : GraphQL.Operation) :
    (normalizeOperation schema operation).fragments = [] := by
  rfl

end NormalForm

end GraphQL
