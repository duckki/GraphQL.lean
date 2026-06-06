import GraphQL.Execution

/-!
Algebra facts for execution field-collection helpers and merged child selections.
-/
namespace GraphQL

namespace Execution

theorem addExecutableFields_append
    (left right : List ExecutableField)
    (groups : List (Name × List ExecutableField)) :
    addExecutableFields (left ++ right) groups
      = addExecutableFields right (addExecutableFields left groups) := by
  induction left generalizing groups with
  | nil =>
      simp [addExecutableFields]
  | cons field rest ih =>
      simp [addExecutableFields]

theorem mergeExecutableGroups_nil_right
    (groups : List (Name × List ExecutableField)) :
    mergeExecutableGroups groups [] = groups := by
  simp [mergeExecutableGroups]

theorem mergeExecutableGroups_append
    (left middle right : List (Name × List ExecutableField)) :
    mergeExecutableGroups left (middle ++ right)
      = mergeExecutableGroups (mergeExecutableGroups left middle) right := by
  simp [mergeExecutableGroups, List.foldl_append]

theorem mergedFieldSelectionSet_nil :
    mergedFieldSelectionSet [] = [] := by
  rfl

theorem mergedFieldSelectionSet_cons
    (field : ExecutableField) (rest : List ExecutableField) :
    mergedFieldSelectionSet (field :: rest)
      = field.selectionSet ++ mergedFieldSelectionSet rest := by
  rfl

theorem mergedFieldSelectionSet_append
    (left right : List ExecutableField) :
    mergedFieldSelectionSet (left ++ right)
      = mergedFieldSelectionSet left ++ mergedFieldSelectionSet right := by
  induction left with
  | nil =>
      simp [mergedFieldSelectionSet]
  | cons field rest ih =>
      simp [mergedFieldSelectionSet, ih, List.append_assoc]

theorem mergedFieldSelectionSet_singleton
    (field : ExecutableField) :
    mergedFieldSelectionSet [field] = field.selectionSet := by
  simp [mergedFieldSelectionSet]

end Execution

end GraphQL
