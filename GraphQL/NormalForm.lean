import GraphQL.Semantic

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

def selectionSetNormal (schema : Schema)
    (selectionSet : List Semantic.Selection) : Prop :=
  selectionSetGroundTyped schema selectionSet ∧ selectionSetNonRedundant selectionSet

def semanticOperationNormal (schema : Schema)
    (operation : Semantic.Operation) : Prop :=
  selectionSetNormal schema operation.selectionSet

def operationNormal (schema : Schema) (operation : GraphQL.Operation) : Prop :=
  semanticOperationNormal schema (Semantic.fromOperation operation)

-- Spec 5.3.2 field merging / 6.3.2 subfield collection: partial normalizer; merges direct
-- same-response-name fields and recursively normalizes child selections when the return
-- type is known.
def mergeFieldSelections (schema : Schema) (fuel : Nat)
    (parentType : Name) (responseName : Name)
    (selectionSet : List Semantic.Selection) : Option Semantic.Selection :=
  match Semantic.SelectionSet.fieldsWithResponseName responseName selectionSet with
  | [] => none
  | first :: matching =>
      match first with
      | .field firstResponseName fieldName arguments directives subselections =>
          let mergedSubselections :=
            subselections ++ Semantic.SelectionSet.mergeSelectionSets matching
          let normalizedSubselections :=
            match schema.fieldReturnType? parentType fieldName with
            | none => mergedSubselections
            | some childType =>
                normalizeSelectionSet schema fuel childType mergedSubselections
          some (.field firstResponseName fieldName arguments directives normalizedSubselections)
      | _ => none

where
  normalizeSelectionSet (schema : Schema) :
      Nat -> Name -> List Semantic.Selection -> List Semantic.Selection
    | 0, _parentType, selectionSet => selectionSet
    | _fuel + 1, _parentType, [] => []
    | fuel + 1, parentType, selection :: rest =>
        match Semantic.Selection.responseName? selection with
        | some responseName =>
            let normalizedRest :=
              normalizeSelectionSet schema fuel parentType
                (Semantic.SelectionSet.withoutFieldsWithResponseName responseName rest)
            match mergeFieldSelections schema fuel parentType responseName (selection :: rest) with
            | some merged => merged :: normalizedRest
            | none => normalizedRest
        | none =>
            let normalizedRest := normalizeSelectionSet schema fuel parentType rest
            match selection with
            | .inlineFragment none [] subselections =>
                normalizeSelectionSet schema fuel parentType (subselections ++ rest)
            | .inlineFragment none directives subselections =>
                .inlineFragment none directives
                  (normalizeSelectionSet schema fuel parentType subselections)
                  :: normalizedRest
            | .inlineFragment (some typeCondition) directives subselections =>
                match schema.lookupType typeCondition with
                | some (.object _) =>
                    .inlineFragment (some typeCondition) directives
                      (normalizeSelectionSet schema fuel typeCondition subselections)
                      :: normalizedRest
                | some (.interface _) | some (.union _) =>
                    let grounded :=
                      (schema.getPossibleTypes typeCondition).map
                        (fun objectName =>
                          Semantic.Selection.inlineFragment (some objectName) directives
                            (normalizeSelectionSet schema fuel objectName subselections))
                    grounded ++ normalizedRest
                | _ => normalizedRest
            | .field .. => normalizedRest

def normalizeSelectionSet (schema : Schema) (fuel : Nat)
    (parentType : Name) (selectionSet : List Semantic.Selection) :
    List Semantic.Selection :=
  mergeFieldSelections.normalizeSelectionSet schema fuel parentType selectionSet

def normalizeSemanticOperation (schema : Schema)
    (operation : Semantic.Operation) : Semantic.Operation :=
  { operation with
    selectionSet := normalizeSelectionSet schema operation.size
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

theorem normalizeSemanticOperation_singleLeaf (schema : Schema) (name : Option Name)
    (rootType : Name) (variableDefinitions : List VariableDefinition)
    (responseName fieldName : Name) (arguments : List Argument) :
    normalizeSemanticOperation schema
      { name := name,
        rootType := rootType,
        variableDefinitions := variableDefinitions,
        selectionSet := [.field responseName fieldName arguments [] []] }
      = { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [.field responseName fieldName arguments [] []] } := by
  cases hfield : schema.fieldReturnType? rootType fieldName <;>
    simp [hfield, normalizeSemanticOperation, normalizeSelectionSet,
      mergeFieldSelections.normalizeSelectionSet, mergeFieldSelections,
      Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
      Semantic.SelectionSet.fieldsWithResponseName,
      Semantic.SelectionSet.withoutFieldsWithResponseName,
      Semantic.SelectionSet.mergeSelectionSets, Semantic.Selection.responseName?,
      Semantic.Selection.subselections]

theorem normalizeSemanticOperation_singleLeafWithDirectives (schema : Schema)
    (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) :
    normalizeSemanticOperation schema
      { name := name,
        rootType := rootType,
        variableDefinitions := variableDefinitions,
        selectionSet := [.field responseName fieldName arguments directives []] }
      = { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [.field responseName fieldName arguments directives []] } := by
  cases hfield : schema.fieldReturnType? rootType fieldName <;>
    simp [hfield, normalizeSemanticOperation, normalizeSelectionSet,
      mergeFieldSelections.normalizeSelectionSet, mergeFieldSelections,
      Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
      Semantic.SelectionSet.fieldsWithResponseName,
      Semantic.SelectionSet.withoutFieldsWithResponseName,
      Semantic.SelectionSet.mergeSelectionSets, Semantic.Selection.responseName?,
      Semantic.Selection.subselections]

theorem normalizeSemanticOperation_twoDistinctLeafNoDirectives (schema : Schema)
    (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (leftResponseName leftFieldName : Name) (leftArguments : List Argument)
    (rightResponseName rightFieldName : Name) (rightArguments : List Argument) :
    leftResponseName ≠ rightResponseName ->
      normalizeSemanticOperation schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [
            .field leftResponseName leftFieldName leftArguments [] [],
            .field rightResponseName rightFieldName rightArguments [] []
          ] }
        = { name := name,
            rootType := rootType,
            variableDefinitions := variableDefinitions,
            selectionSet := [
              .field leftResponseName leftFieldName leftArguments [] [],
              .field rightResponseName rightFieldName rightArguments [] []
            ] } := by
  intro hdistinct
  have hdistinct' : rightResponseName ≠ leftResponseName := Ne.symm hdistinct
  cases hleft : schema.fieldReturnType? rootType leftFieldName <;>
    cases hright : schema.fieldReturnType? rootType rightFieldName <;>
      simp [hleft, hright, hdistinct', normalizeSemanticOperation,
        normalizeSelectionSet, mergeFieldSelections.normalizeSelectionSet,
        mergeFieldSelections, Semantic.Operation.size, Semantic.SelectionSet.size,
        Semantic.Selection.size, Semantic.SelectionSet.fieldsWithResponseName,
        Semantic.SelectionSet.withoutFieldsWithResponseName,
        Semantic.SelectionSet.mergeSelectionSets, Semantic.Selection.responseName?,
        Semantic.Selection.subselections]

theorem normalizeSemanticOperation_inlineFragmentSingleLeaf (schema : Schema)
    (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (responseName fieldName : Name) (arguments : List Argument) :
    normalizeSemanticOperation schema
      { name := name,
        rootType := rootType,
        variableDefinitions := variableDefinitions,
        selectionSet := [.inlineFragment none []
          [.field responseName fieldName arguments [] []]] }
      = { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [.field responseName fieldName arguments [] []] } := by
  cases hfield : schema.fieldReturnType? rootType fieldName <;>
    simp [hfield, normalizeSemanticOperation, normalizeSelectionSet,
      mergeFieldSelections.normalizeSelectionSet, mergeFieldSelections,
      Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
      Semantic.SelectionSet.fieldsWithResponseName,
      Semantic.SelectionSet.withoutFieldsWithResponseName,
      Semantic.SelectionSet.mergeSelectionSets, Semantic.Selection.responseName?,
      Semantic.Selection.subselections]

theorem normalizeSemanticOperation_typedInlineFragmentSingleLeafObjectWithDirectives
    (schema : Schema) (name : Option Name) (rootType typeCondition : Name)
    (variableDefinitions : List VariableDefinition)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (objectType : ObjectType) :
    schema.lookupType typeCondition = some (.object objectType) ->
      normalizeSemanticOperation schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [.inlineFragment (some typeCondition) directives
            [.field responseName fieldName arguments [] []]] }
        = { name := name,
            rootType := rootType,
            variableDefinitions := variableDefinitions,
            selectionSet := [.inlineFragment (some typeCondition) directives
              [.field responseName fieldName arguments [] []]] } := by
  intro htype
  cases hfield : schema.fieldReturnType? typeCondition fieldName <;>
    simp [htype, hfield, normalizeSemanticOperation, normalizeSelectionSet,
      mergeFieldSelections.normalizeSelectionSet, mergeFieldSelections,
      Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
      Semantic.SelectionSet.fieldsWithResponseName,
      Semantic.SelectionSet.withoutFieldsWithResponseName,
      Semantic.SelectionSet.mergeSelectionSets, Semantic.Selection.responseName?,
      Semantic.Selection.subselections]

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
