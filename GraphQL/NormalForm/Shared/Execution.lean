import GraphQL.NormalForm.Shared.DirectiveFree
import GraphQL.Execution

/-!
Directive-free execution collection facts shared by NormalForm proof modules.
-/
namespace GraphQL

namespace Execution

-- Proof-only projection of the child selections contributed by a grouped field list.
-- Runtime execution uses `collectSubfields`; normal-form proofs use this syntactic
-- view when relating field groups back to validation-time selection sets.
def mergedFieldSelectionSet : List ExecutableField -> List Selection
  | [] => []
  | field :: rest => field.selectionSet ++ mergedFieldSelectionSet rest

@[simp] theorem mergedFieldSelectionSet_nil :
    mergedFieldSelectionSet [] = [] := by
  rfl

@[simp] theorem mergedFieldSelectionSet_cons
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

@[simp] theorem mergedFieldSelectionSet_singleton
    (field : ExecutableField) :
    mergedFieldSelectionSet [field] = field.selectionSet := by
  simp [mergedFieldSelectionSet]

@[simp] theorem mergedFieldSelectionSet_ite {c : Prop} [Decidable c]
    (left right : List ExecutableField) :
    mergedFieldSelectionSet (if c then left else right) =
      if c then mergedFieldSelectionSet left
      else mergedFieldSelectionSet right := by
  by_cases hc : c
  · simp [hc]
  · simp [hc]

def selectionSetExecutableField (selectionSet : List Selection) : ExecutableField :=
  {
    parentType := "",
    responseName := "",
    fieldName := "",
    arguments := [],
    selectionSet := selectionSet
  }

def selectionExecutableField (selection : Selection) : ExecutableField :=
  selectionSetExecutableField [selection]

instance : Coe Selection ExecutableField where
  coe selection := selectionExecutableField selection

instance : Coe (List Selection) (List ExecutableField) where
  coe selectionSet := selectionSet.map selectionExecutableField

@[simp] theorem mergedFieldSelectionSet_map_selectionExecutableField
    (selectionSet : List Selection) :
    mergedFieldSelectionSet (selectionSet.map selectionExecutableField)
      = selectionSet := by
  induction selectionSet with
  | nil =>
      simp
  | cons selection rest ih =>
      simp [selectionExecutableField, selectionSetExecutableField, ih]

@[simp] theorem mergedFieldSelectionSet_selectionExecutableField_map
    (selectionSet : List Selection) :
    mergedFieldSelectionSet (selectionExecutableField <$> selectionSet)
      = selectionSet := by
  exact mergedFieldSelectionSet_map_selectionExecutableField selectionSet

@[simp] theorem mergedFieldSelectionSet_map_selectionExecutableField_comp
    {α : Type} (items : List α) (f : α -> Selection) :
    mergedFieldSelectionSet
      (items.map (fun item => selectionExecutableField (f item)))
      = items.map f := by
  induction items with
  | nil =>
      simp
  | cons item rest ih =>
      simp [selectionExecutableField, selectionSetExecutableField]
      simpa [selectionExecutableField, selectionSetExecutableField] using ih

@[simp] theorem mergedFieldSelectionSet_map_selectionExecutableField_append
    (left right : List Selection) :
    mergedFieldSelectionSet
      (left.map selectionExecutableField ++ right.map selectionExecutableField)
      = left ++ right := by
  simp [mergedFieldSelectionSet_append]

end Execution

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
