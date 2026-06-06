import GraphQL.Execution

/-!
Spec reference: GraphQL September 2025.
- 5.3.2 Field Selection Merging and 6.3.2 Field Collection: normalization merges
  same-response-name field subselections in the spirit of GraphQL's merge/collect
  behavior.
- 5.5.2.3 Fragment Spread Is Possible and `GetPossibleTypes`: abstract type conditions are
  grounded through possible object types.
- Fidelity note: GraphQL does not define this normal form. This is a project-specific
  canonicalization scaffold; it is partial, fuel-bounded, and does not yet prove semantic
  preservation.
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

mutual
  -- Spec 6.3.2 field collection helper: finds fields with one response name, descending
  -- through fragments that can contribute selections in the current type scope.
  def validFieldsWithResponseName (schema : Schema) :
      Nat -> Name -> Name -> List Semantic.Selection -> List Semantic.Selection
    | 0, _parentType, _responseName, _selectionSet => []
    | _fuel + 1, _parentType, _responseName, [] => []
    | fuel + 1, parentType, responseName, selection :: rest =>
        match selection with
        | .field fieldResponseName _fieldName _arguments _directives _selectionSet =>
            let restFields :=
              validFieldsWithResponseName schema fuel parentType responseName rest
            if fieldResponseName == responseName then
              selection :: restFields
            else
              restFields
        | .inlineFragment none _directives selectionSet =>
            validFieldsWithResponseName schema fuel parentType responseName selectionSet
              ++ validFieldsWithResponseName schema fuel parentType responseName rest
        | .inlineFragment (some typeCondition) _directives selectionSet =>
            let restFields :=
              validFieldsWithResponseName schema fuel parentType responseName rest
            if schema.typesOverlapBool parentType typeCondition then
              validFieldsWithResponseName schema fuel parentType responseName selectionSet
                ++ restFields
            else
              restFields

  -- Spec 6.3.2 field collection helper: removes fields with one response name recursively
  -- so later fragment lifting cannot reintroduce a duplicate field group.
  def withoutFieldsWithResponseName (schema : Schema) :
      Nat -> Name -> List Semantic.Selection -> List Semantic.Selection
    | 0, _responseName, _selectionSet => []
    | _fuel + 1, _responseName, [] => []
    | fuel + 1, responseName, selection :: rest =>
        match selection with
        | .field fieldResponseName _fieldName _arguments _directives _selectionSet =>
            let filteredRest :=
              withoutFieldsWithResponseName schema fuel responseName rest
            if fieldResponseName == responseName then
              filteredRest
            else
              selection :: filteredRest
        | .inlineFragment typeCondition directives selectionSet =>
            .inlineFragment typeCondition directives
              (withoutFieldsWithResponseName schema fuel responseName selectionSet)
              :: withoutFieldsWithResponseName schema fuel responseName rest

  -- GraphCoQL-style grounding: object return types normalize directly; abstract
  -- interface/union return types are specialized into one object fragment per possible type.
  def normalizeFieldSelectionSet (schema : Schema) :
      Nat -> Name -> List Semantic.Selection -> List Semantic.Selection
    | 0, _returnType, _selectionSet => []
    | fuel + 1, returnType, selectionSet =>
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema fuel returnType selectionSet
        else
          (schema.getPossibleTypes returnType).map
            (fun objectType =>
              .inlineFragment (some objectType) []
                (normalizeSelectionSet schema fuel objectType selectionSet))

  -- Spec 5.3.2 field merging / 6.3.2 subfield collection: partial normalizer; merges
  -- same-response-name fields, recursively normalizes child selections, and grounds
  -- abstract field return types through possible object types. The proof path assumes
  -- directive-free source operations, so this is not directive-sensitive.
  def normalizeSelectionSet (schema : Schema) :
      Nat -> Name -> List Semantic.Selection -> List Semantic.Selection
    | 0, _parentType, _selectionSet => []
    | _fuel + 1, _parentType, [] => []
    | fuel + 1, parentType, selection :: rest =>
        match selection with
        | .field responseName fieldName arguments directives subselections =>
            let normalizedRest :=
              normalizeSelectionSet schema fuel parentType
                (withoutFieldsWithResponseName schema fuel responseName rest)
            match schema.lookupField parentType fieldName with
            | none => normalizedRest
            | some fieldDefinition =>
                let matching :=
                  validFieldsWithResponseName schema fuel parentType responseName rest
                let mergedSubselections :=
                  subselections ++ Semantic.SelectionSet.mergeSelectionSets matching
                .field responseName fieldName arguments directives
                    (normalizeFieldSelectionSet schema fuel
                      fieldDefinition.outputType.namedType mergedSubselections)
                  :: normalizedRest
        | .inlineFragment none _directives subselections =>
            normalizeSelectionSet schema fuel parentType (subselections ++ rest)
        | .inlineFragment (some typeCondition) _directives subselections =>
            let normalizedRest := normalizeSelectionSet schema fuel parentType rest
            if schema.typesOverlapBool parentType typeCondition then
              normalizeSelectionSet schema fuel parentType (subselections ++ rest)
            else
              normalizedRest
end

-- Spec-inspired semantic normalizer: non-spec wrapper around selection-set
-- normalization.
def normalizeSemanticOperation (schema : Schema)
    (operation : Semantic.Operation) : Semantic.Operation :=
  { operation with
    selectionSet := normalizeSelectionSet schema (operation.size * 2 + 1)
      operation.rootType operation.selectionSet }

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

def semanticOperationsEquivalentWithFuel (schema : Schema) (fuel : Nat)
    (left right : Semantic.Operation) : Prop :=
  ∀ resolvers variableValues source,
    Execution.executeSelectionSet schema resolvers variableValues fuel
      left.rootType source left.selectionSet
      =
    Execution.executeSelectionSet schema resolvers variableValues fuel
      right.rootType source right.selectionSet

def groundTypeNormalFormSemanticsPreserved (schema : Schema)
    (operation : Semantic.Operation) : Prop :=
  semanticOperationsEquivalentWithFuel schema
    (Execution.executeSemanticQueryFuel operation)
    operation (normalizeSemanticOperation schema operation)

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
