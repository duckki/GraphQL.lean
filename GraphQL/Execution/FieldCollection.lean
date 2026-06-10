import GraphQL.Execution

/-!
Algebra facts for execution field-collection helpers and collected subfields.
-/
namespace GraphQL

namespace Execution

theorem mergeExecutableGroups_nil_right
    (groups : List (Name × List ExecutableField)) :
    mergeExecutableGroups groups [] = groups := by
  simp [mergeExecutableGroups]

theorem mergeExecutableGroups_append
    (left middle right : List (Name × List ExecutableField)) :
    mergeExecutableGroups left (middle ++ right)
      = mergeExecutableGroups (mergeExecutableGroups left middle) right := by
  simp [mergeExecutableGroups, List.foldl_append]

theorem collectSubfields_nil {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (objectType : Name) (objectValue : Value ObjectIdentity) :
    collectSubfields schema variableValues objectType objectValue [] = [] := by
  rfl

theorem collectSubfields_cons {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (objectType : Name) (objectValue : Value ObjectIdentity)
    (field : ExecutableField) (rest : List ExecutableField) :
    collectSubfields schema variableValues objectType objectValue
        (field :: rest)
      =
        mergeExecutableGroups
          (collectFields schema variableValues objectType objectValue
            field.selectionSet)
          (collectSubfields schema variableValues objectType objectValue
            rest) := by
  rfl

theorem executeCollectedFields_cons_eq_of_parts
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (source : Value ObjectIdentity)
    (leftHead rightHead : Name × List ExecutableField)
    (leftTail rightTail : List (Name × List ExecutableField)) :
    executeField schema resolvers variableValues depth source
        leftHead.fst leftHead.snd
      =
      executeField schema resolvers variableValues depth source
        rightHead.fst rightHead.snd ->
    executeCollectedFields schema resolvers variableValues depth source
        leftTail
      =
      executeCollectedFields schema resolvers variableValues depth source
        rightTail ->
      executeCollectedFields schema resolvers variableValues depth source
          (leftHead :: leftTail)
        =
        executeCollectedFields schema resolvers variableValues depth source
          (rightHead :: rightTail) := by
  intro hhead htail
  cases leftHead with
  | mk leftResponseName leftFields =>
      cases rightHead with
      | mk rightResponseName rightFields =>
          simp [executeCollectedFields, hhead, htail]

theorem executeSelectionSet_eq_of_collectFields_head_parts
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Value ObjectIdentity)
    (left right : List Selection)
    (leftGroup rightGroup : Name × List ExecutableField)
    (leftRest rightRest : List (Name × List ExecutableField)) :
    collectFields schema variableValues parentType source left
      = leftGroup :: leftRest ->
    collectFields schema variableValues parentType source right
      = rightGroup :: rightRest ->
    executeField schema resolvers variableValues depth source
      leftGroup.fst leftGroup.snd
      =
    executeField schema resolvers variableValues depth source
      rightGroup.fst rightGroup.snd ->
    executeCollectedFields schema resolvers variableValues depth
      source leftRest
      =
    executeCollectedFields schema resolvers variableValues depth
      source rightRest ->
      executeSelectionSet schema resolvers variableValues depth
        parentType source left
      =
      executeSelectionSet schema resolvers variableValues depth
        parentType source right := by
  intro hleftCollect hrightCollect hhead htail
  simp [executeSelectionSet, executeRootSelectionSet, hleftCollect,
    hrightCollect]
  exact executeCollectedFields_cons_eq_of_parts schema resolvers
    variableValues depth source leftGroup rightGroup leftRest rightRest
    hhead htail

theorem executeField_same_head_eq_of_completeValue
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (source : Value ObjectIdentity)
    (responseName parentType fieldName : Name) (arguments : List Argument)
    (leftSelectionSet rightSelectionSet : List Selection)
    (leftFields rightFields : List ExecutableField) :
    let leftField : ExecutableField :=
      {
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := leftSelectionSet
      }
    let rightField : ExecutableField :=
      {
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := rightSelectionSet
      }
    let resolved :=
      resolvers.resolve parentType fieldName arguments source
    let childType :=
      (schema.fieldReturnType? parentType fieldName).getD fieldName
    completeValue schema resolvers variableValues depth childType
      (leftField :: leftFields) resolved
      =
    completeValue schema resolvers variableValues depth childType
      (rightField :: rightFields) resolved ->
      executeField schema resolvers variableValues (depth + 1)
        source responseName (leftField :: leftFields)
      =
      executeField schema resolvers variableValues (depth + 1)
        source responseName (rightField :: rightFields) := by
  intro leftField rightField resolved childType hcomplete
  simp [executeField, leftField, rightField, resolved, childType,
    hcomplete]

theorem executeSelectionSet_field_head_same_group_eq_of_completeValue
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (fieldDepth : Nat) (parentType : Name)
    (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (leftSelectionSet rightSelectionSet left right : List Selection)
    (leftFields rightFields : List ExecutableField)
    (leftRest rightRest : List (Name × List ExecutableField)) :
    let leftField : ExecutableField :=
      {
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := leftSelectionSet
      }
    let rightField : ExecutableField :=
      {
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := rightSelectionSet
      }
    collectFields schema variableValues parentType source left
      =
    (responseName, leftField :: leftFields) :: leftRest ->
    collectFields schema variableValues parentType source right
      =
    (responseName, rightField :: rightFields) :: rightRest ->
    completeValue schema resolvers variableValues fieldDepth
      ((schema.fieldReturnType? parentType fieldName).getD fieldName)
      (leftField :: leftFields)
      (resolvers.resolve parentType fieldName arguments source)
      =
    completeValue schema resolvers variableValues fieldDepth
      ((schema.fieldReturnType? parentType fieldName).getD fieldName)
      (rightField :: rightFields)
      (resolvers.resolve parentType fieldName arguments source) ->
    executeCollectedFields schema resolvers variableValues
      (fieldDepth + 1) source leftRest
      =
    executeCollectedFields schema resolvers variableValues
      (fieldDepth + 1) source rightRest ->
      executeSelectionSet schema resolvers variableValues
        (fieldDepth + 1) parentType source left
      =
      executeSelectionSet schema resolvers variableValues
        (fieldDepth + 1) parentType source right := by
  intro leftField rightField hleftCollect hrightCollect hcomplete htail
  apply executeSelectionSet_eq_of_collectFields_head_parts schema resolvers
    variableValues (fieldDepth + 1) parentType source left right
    (responseName, leftField :: leftFields)
    (responseName, rightField :: rightFields) leftRest rightRest
    hleftCollect hrightCollect
  · exact executeField_same_head_eq_of_completeValue schema resolvers
      variableValues fieldDepth source responseName parentType fieldName
      arguments leftSelectionSet rightSelectionSet leftFields rightFields
      hcomplete
  · exact htail
end Execution

end GraphQL
