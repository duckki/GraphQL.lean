import GraphQL.Operation

/-!
Spec reference: GraphQL September 2025.
- 5.3.2 Field Selection Merging: models same-response-name compatibility via
  response-shape compatibility, field-name/argument equality when required by the spec's
  parent-type condition, and recursive subfield merge checks.
- 6.3.2 Field Collection: provides a validation-time field collector for merge analysis,
  distinct from execution-time field collection.
- Fidelity note: validation-time collection ignores executable directives and uses a fuel
  bound; it also follows fragments by declared type condition without the execution
  algorithm's runtime `DoesFragmentTypeApply` filtering.
-/
namespace GraphQL

namespace FieldMerge

-- Spec 5.3.2 `FieldsInSetCanMerge` field-pair context: non-spec helper carrying the
-- parent type and field data needed by merge checks.
structure ScopedField where
  parentType : Name
  responseName : Name
  fieldName : Name
  arguments : List Argument
  outputType : TypeRef
  selectionSet : List Selection
deriving Repr

-- Spec 5.3.2 `SameResponseShape`: mostly faithful for wrapping structure and leaf
-- named-type equality, using the modeled schema's leaf/output predicates.
def sameResponseShape (schema : Schema) : TypeRef -> TypeRef -> Prop
  | .nonNull left, .nonNull right => sameResponseShape schema left right
  | .nonNull _, _ => False
  | _, .nonNull _ => False
  | .list left, .list right => sameResponseShape schema left right
  | .list _, _ => False
  | _, .list _ => False
  | .named left, .named right =>
      schema.isOutputType left
        ∧ schema.isOutputType right
        ∧ ((schema.isLeafType left ∨ schema.isLeafType right) -> left = right)

-- Spec 5.3.2 `CollectFieldsAndFragmentNames` / 6.3.2 `CollectFields`: partial validation
-- helper; it expands modeled fragments but does not apply directives or runtime
-- type-condition filtering.
def collectFields (schema : Schema) (fragments : List FragmentDefinition) :
    Nat -> Name -> List Selection -> List ScopedField
  | 0, _parentType, _selectionSet => []
  | _fuel + 1, _parentType, [] => []
  | fuel + 1, parentType, selection :: rest =>
      let current :=
        match selection with
        | .field responseName fieldName arguments _directives selectionSet =>
            match schema.lookupField parentType fieldName with
            | none => []
            | some fieldDefinition =>
                [{
                  parentType := parentType,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  outputType := fieldDefinition.outputType,
                  selectionSet := selectionSet
                }]
        | .fragmentSpread fragmentName _directives =>
            match FragmentDefinition.find? fragments fragmentName with
            | none => []
            | some fragment =>
                collectFields schema fragments fuel fragment.typeCondition fragment.selectionSet
        | .inlineFragment none _directives selectionSet =>
            collectFields schema fragments fuel parentType selectionSet
        | .inlineFragment (some typeCondition) _directives selectionSet =>
            collectFields schema fragments fuel typeCondition selectionSet
      current ++ collectFields schema fragments fuel parentType rest

-- Spec 5.3.2 `FieldsInSetCanMerge`: partial; captures pairwise response-shape, same
-- field/arguments on overlapping parent types, and recursive merged subselection checks.
def fieldsInSetCanMerge (schema : Schema) (fragments : List FragmentDefinition) :
    Nat -> Name -> List Selection -> Prop
  | 0, _parentType, _selectionSet => True
  | fuel + 1, parentType, selectionSet =>
      let fields := collectFields schema fragments (fuel + 1) parentType selectionSet
      ∀ left, left ∈ fields ->
        ∀ right, right ∈ fields ->
          left.responseName = right.responseName ->
            fieldsForNameCanMerge fuel left right

where
  -- Spec 5.3.2 same-response-name field pair check inside `FieldsInSetCanMerge`.
  fieldsForNameCanMerge (fuel : Nat) (left right : ScopedField) : Prop :=
    sameResponseShape schema left.outputType right.outputType
      ∧ ((left.parentType = right.parentType
          ∨ ¬ schema.objectType left.parentType
          ∨ ¬ schema.objectType right.parentType) ->
        left.fieldName = right.fieldName
          ∧ Argument.argumentsEquivalent left.arguments right.arguments)
      ∧ fieldsInSetCanMerge schema fragments fuel left.outputType.namedType
        (left.selectionSet ++ right.selectionSet)

end FieldMerge

end GraphQL
