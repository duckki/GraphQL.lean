import GraphQL.Semantic

namespace GraphQL

namespace NormalForm

def selectionsAllFields (selectionSet : List Semantic.Selection) : Prop :=
  ∀ selection, selection ∈ selectionSet -> Semantic.Selection.isField selection

def selectionsAllInlineFragments (selectionSet : List Semantic.Selection) : Prop :=
  ∀ selection, selection ∈ selectionSet ->
    Semantic.Selection.isInlineFragment selection

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

def inlineFragmentTypeConditionsNodup
    (selectionSet : List Semantic.Selection) : Prop :=
  (selectionSet.filterMap (fun selection =>
    match selection with
    | .inlineFragment (some typeCondition) _directives _selectionSet =>
        some typeCondition
    | _ => none)).Nodup

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
                      (schema.possibleObjectNames typeCondition).map
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

def normalizeOperation (schema : Schema) (operation : GraphQL.Operation) :
    GraphQL.Operation :=
  (normalizeSemanticOperation schema (Semantic.fromOperation operation)).toOperation

theorem normalizeOperation_fragments_empty (schema : Schema)
    (operation : GraphQL.Operation) :
    (normalizeOperation schema operation).fragments = [] := by
  rfl

end NormalForm

end GraphQL
