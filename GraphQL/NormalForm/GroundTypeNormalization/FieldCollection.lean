import GraphQL.NormalForm.GroundTypeNormalization

/-!
Field-collection helper lemmas for directive-free ground-type normalization.

This module separates execution-facing collection facts from the structural normal-form
proofs in `GraphQL.NormalForm.GroundTypeNormalization`.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem collectFields_nil
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value) :
    Execution.collectFields schema variableValues parentType source [] = [] := by
  rfl

theorem collectFields_cons
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value)
    (selection : Selection) (rest : List Selection) :
    Execution.collectFields schema variableValues parentType source
      (selection :: rest)
      =
    Execution.mergeExecutableGroups
      (Execution.collectSelection schema variableValues parentType source selection)
      (Execution.collectFields schema variableValues parentType source rest) := by
  rfl

theorem collectFields_field_noDirectives
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet rest : List Selection) :
    Execution.collectFields schema variableValues parentType source
      (Selection.field responseName fieldName arguments [] selectionSet :: rest)
      =
    Execution.mergeExecutableGroups
      [(responseName, [{
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := selectionSet
      }])]
      (Execution.collectFields schema variableValues parentType source rest) := by
  simp [collectFields_cons, collectSelection_field_noDirectives]

theorem collectFields_inlineFragment_none_directiveFree
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Execution.collectFields schema variableValues parentType source
      (Selection.inlineFragment none [] selectionSet :: rest)
      =
    Execution.mergeExecutableGroups
      (Execution.collectFields schema variableValues parentType source selectionSet)
      (Execution.collectFields schema variableValues parentType source rest) := by
  simp [collectFields_cons, collectSelection_inlineFragment_none_noDirectives]

theorem collectFields_inlineFragment_some_directiveFree_apply
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType typeCondition : Name) (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Execution.doesFragmentTypeApplyBool schema parentType source typeCondition = true ->
      Execution.collectFields schema variableValues parentType source
        (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest)
        =
      Execution.mergeExecutableGroups
        (Execution.collectFields schema variableValues parentType source selectionSet)
        (Execution.collectFields schema variableValues parentType source rest) := by
  intro happly
  simp [collectFields_cons, collectSelection_inlineFragment_some_noDirectives,
    happly]

theorem collectFields_inlineFragment_some_directiveFree_skip
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType typeCondition : Name) (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Execution.doesFragmentTypeApplyBool schema parentType source typeCondition = false ->
      Execution.collectFields schema variableValues parentType source
        (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest)
        =
      Execution.mergeExecutableGroups []
        (Execution.collectFields schema variableValues parentType source rest) := by
  intro hskip
  simp [collectFields_cons, collectSelection_inlineFragment_some_noDirectives,
    hskip]

end GroundTypeNormalization

end NormalForm

end GraphQL
