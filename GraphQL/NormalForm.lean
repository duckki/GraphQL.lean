import GraphQL.Operation

namespace GraphQL

namespace NormalForm

def selectionsAllFields (selectionSet : List Selection) : Prop :=
  ∀ selection, selection ∈ selectionSet -> QueryAux.isField selection

def selectionsAllInlineFragments (selectionSet : List Selection) : Prop :=
  ∀ selection, selection ∈ selectionSet -> QueryAux.isInlineFragment selection

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
    | .fragmentSpread _fragmentName _directives => True

  def selectionSetGroundTyped (schema : Schema) (selectionSet : List Selection) : Prop :=
    (selectionsAllFields selectionSet ∨ selectionsAllInlineFragments selectionSet)
      ∧ ∀ selection, selection ∈ selectionSet -> selectionGroundTyped schema selection
end

def responseNamesNodup (selectionSet : List Selection) : Prop :=
  (selectionSet.filterMap QueryAux.responseName?).Nodup

def inlineFragmentTypeConditionsNodup (selectionSet : List Selection) : Prop :=
  (selectionSet.filterMap (fun selection =>
    match selection with
    | .inlineFragment (some typeCondition) _directives _selectionSet => some typeCondition
    | _ => none)).Nodup

mutual
  def selectionNonRedundant : Selection -> Prop
    | .field _responseName _fieldName _arguments _directives selectionSet =>
        selectionSetNonRedundant selectionSet
    | .inlineFragment _typeCondition _directives selectionSet =>
        selectionSetNonRedundant selectionSet
    | .fragmentSpread _fragmentName _directives => True

  def selectionSetNonRedundant (selectionSet : List Selection) : Prop :=
    responseNamesNodup selectionSet
      ∧ inlineFragmentTypeConditionsNodup selectionSet
      ∧ ∀ selection, selection ∈ selectionSet -> selectionNonRedundant selection
end

def selectionSetNormal (schema : Schema) (selectionSet : List Selection) : Prop :=
  selectionSetGroundTyped schema selectionSet ∧ selectionSetNonRedundant selectionSet

def operationNormal (schema : Schema) (operation : Operation) : Prop :=
  selectionSetNormal schema operation.selectionSet

def mergeFieldSelections (schema : Schema) (fragments : List FragmentDefinition)
    (fuel : Nat) (parentType : Name) (responseName : Name)
    (selectionSet : List Selection) : Option Selection :=
  match QueryAux.fieldsWithResponseName responseName selectionSet with
  | [] => none
  | first :: matching =>
      match first with
      | .field firstResponseName fieldName arguments directives subselections =>
          let mergedSubselections :=
            subselections ++ QueryAux.mergeSelectionSets matching
          let normalizedSubselections :=
            match schema.fieldReturnType? parentType fieldName with
            | none => mergedSubselections
            | some childType =>
                normalizeSelectionSet schema fragments fuel childType mergedSubselections
          some (.field firstResponseName fieldName arguments directives normalizedSubselections)
      | _ => none

where
  normalizeSelectionSet (schema : Schema) (fragments : List FragmentDefinition) :
      Nat -> Name -> List Selection -> List Selection
    | 0, _parentType, selectionSet => selectionSet
    | _fuel + 1, _parentType, [] => []
    | fuel + 1, parentType, selection :: rest =>
        match QueryAux.responseName? selection with
        | some responseName =>
            let normalizedRest :=
              normalizeSelectionSet schema fragments fuel parentType
                (QueryAux.withoutFieldsWithResponseName responseName rest)
            match mergeFieldSelections schema fragments fuel parentType responseName (selection :: rest) with
            | some merged => merged :: normalizedRest
            | none => normalizedRest
        | none =>
            let normalizedRest := normalizeSelectionSet schema fragments fuel parentType rest
            match selection with
            | .fragmentSpread fragmentName _directives =>
                match QueryAux.findFragment? fragments fragmentName with
                | none => normalizedRest
                | some fragment =>
                    normalizeSelectionSet schema fragments fuel fragment.typeCondition
                      (fragment.selectionSet ++ rest)
            | .inlineFragment none _directives subselections =>
                normalizeSelectionSet schema fragments fuel parentType (subselections ++ rest)
            | .inlineFragment (some typeCondition) directives subselections =>
                match schema.lookupType typeCondition with
                | some (.object _) =>
                    .inlineFragment (some typeCondition) directives
                      (normalizeSelectionSet schema fragments fuel typeCondition subselections)
                      :: normalizedRest
                | some (.interface _) | some (.union _) =>
                    let grounded :=
                      (schema.possibleObjectNames typeCondition).map
                        (fun objectName =>
                          Selection.inlineFragment (some objectName) directives
                            (normalizeSelectionSet schema fragments fuel objectName subselections))
                    grounded ++ normalizedRest
                | _ => normalizedRest
            | .field .. => normalizedRest

def normalizeSelectionSet (schema : Schema) (fragments : List FragmentDefinition)
    (fuel : Nat) (parentType : Name) (selectionSet : List Selection) : List Selection :=
  mergeFieldSelections.normalizeSelectionSet schema fragments fuel parentType selectionSet

def normalizeOperation (schema : Schema) (operation : Operation) : Operation :=
  { operation with
    selectionSet := normalizeSelectionSet schema operation.fragments operation.size
      operation.rootType operation.selectionSet }

end NormalForm

end GraphQL
