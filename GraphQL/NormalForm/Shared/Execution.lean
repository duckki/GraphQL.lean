import GraphQL.NormalForm.Shared.DirectiveFree
import GraphQL.Execution

/-!
Directive-free execution collection facts shared by NormalForm proof modules.
-/
namespace GraphQL

namespace NormalForm


variable {ObjectIdentity : Type}

theorem selectionDirectivesAllowBool_nil
    (variableValues : Execution.VariableValues) :
    Execution.selectionDirectivesAllowBool variableValues [] = true := by
  rfl

theorem selectionDirectiveFree_directivesAllowBool
    (variableValues : Execution.VariableValues) {selection : Selection} :
    selectionDirectiveFree selection ->
      match selection with
      | .field _responseName _fieldName _arguments directives _selectionSet =>
          Execution.selectionDirectivesAllowBool variableValues directives = true
      | .inlineFragment _typeCondition directives _selectionSet =>
          Execution.selectionDirectivesAllowBool variableValues directives = true := by
  intro hfree
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      have hdirectives : directives = [] := hfree.1
      subst directives
      rfl
  | inlineFragment typeCondition directives selectionSet =>
      have hdirectives : directives = [] := hfree.1
      subst directives
      rfl

theorem collectSelection_field_noDirectives
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet : List Selection) :
    Execution.collectSelection schema variableValues parentType source
      (Selection.field responseName fieldName arguments [] selectionSet)
      =
      [(responseName, [{
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := selectionSet
      }])] := by
  simp [Execution.collectSelection, Execution.selectionDirectivesAllowBool]

theorem collectSelection_inlineFragment_none_noDirectives
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value ObjectIdentity)
    (selectionSet : List Selection) :
    Execution.collectSelection schema variableValues parentType source
      (Selection.inlineFragment none [] selectionSet)
      =
      Execution.collectFields schema variableValues parentType source
        selectionSet := by
  simp [Execution.collectSelection, Execution.selectionDirectivesAllowBool]

theorem collectSelection_inlineFragment_some_noDirectives
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType typeCondition : Name) (source : Execution.Value ObjectIdentity)
    (selectionSet : List Selection) :
    Execution.collectSelection schema variableValues parentType source
      (Selection.inlineFragment (some typeCondition) [] selectionSet)
      =
      if Execution.doesFragmentTypeApplyBool schema parentType source
          typeCondition then
        Execution.collectFields schema variableValues parentType source
          selectionSet
      else
        [] := by
  simp [Execution.collectSelection, Execution.selectionDirectivesAllowBool]


end NormalForm

end GraphQL
