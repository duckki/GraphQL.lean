import GraphQL.Schema

namespace GraphQL

namespace FieldMerge

structure ScopedField where
  parentType : Name
  responseName : Name
  fieldName : Name
  arguments : List Argument
  outputType : TypeRef
  selectionSet : List Selection
deriving Repr

def fieldShapeCompatible (schema : Schema) : TypeRef -> TypeRef -> Prop
  | .nonNull left, .nonNull right => fieldShapeCompatible schema left right
  | .nonNull _, _ => False
  | _, .nonNull _ => False
  | .list left, .list right => fieldShapeCompatible schema left right
  | .list _, _ => False
  | _, .list _ => False
  | .named left, .named right =>
      schema.outputType left
        ∧ schema.outputType right
        ∧ ((schema.leafType left ∨ schema.leafType right) -> left = right)

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
            match fragments.find? (fun fragment => fragment.name == fragmentName) with
            | none => []
            | some fragment =>
                collectFields schema fragments fuel fragment.typeCondition fragment.selectionSet
        | .inlineFragment none _directives selectionSet =>
            collectFields schema fragments fuel parentType selectionSet
        | .inlineFragment (some typeCondition) _directives selectionSet =>
            collectFields schema fragments fuel typeCondition selectionSet
      current ++ collectFields schema fragments fuel parentType rest

def selectionSetFieldsCanMerge (schema : Schema) (fragments : List FragmentDefinition) :
    Nat -> Name -> List Selection -> Prop
  | 0, _parentType, _selectionSet => True
  | fuel + 1, parentType, selectionSet =>
      let fields := collectFields schema fragments (fuel + 1) parentType selectionSet
      ∀ left, left ∈ fields ->
        ∀ right, right ∈ fields ->
          left.responseName = right.responseName ->
            scopedFieldsPairCanMerge fuel left right

where
  scopedFieldsPairCanMerge (fuel : Nat) (left right : ScopedField) : Prop :=
    fieldShapeCompatible schema left.outputType right.outputType
      ∧ (schema.typesOverlap left.parentType right.parentType ->
        left.fieldName = right.fieldName ∧ left.arguments = right.arguments)
      ∧ selectionSetFieldsCanMerge schema fragments fuel left.outputType.namedType
        (left.selectionSet ++ right.selectionSet)

end FieldMerge

end GraphQL
