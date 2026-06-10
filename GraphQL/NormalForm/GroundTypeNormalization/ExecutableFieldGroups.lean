import GraphQL.NormalForm
import GraphQL.Execution
import GraphQL.Validation.FieldMerge

/-!
Executable field-group invariants used by ground-type normalization proofs.
-/
namespace GraphQL

namespace Execution

-- Proof-only projection of the child selections contributed by a grouped field list.
-- Runtime execution now uses `collectSubfields`; normal-form proofs still need this
-- syntactic view when relating field groups back to validation-time selection sets.
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
    mergedFieldSelectionSet (items.map (fun item => selectionExecutableField (f item)))
      = items.map f := by
  induction items with
  | nil =>
      simp
  | cons item rest ih =>
      simp [selectionExecutableField, selectionSetExecutableField]
      simpa [selectionExecutableField, selectionSetExecutableField] using ih

end Execution

namespace NormalForm

namespace GroundTypeNormalization

def executableGroupNamesNodup :
    List (Name × List Execution.ExecutableField) -> Prop
  | [] => True
  | (responseName, _fields) :: rest =>
      responseName ∉ rest.map Prod.fst ∧ executableGroupNamesNodup rest

def executableGroupNamesDisjoint
    (left right : List (Name × List Execution.ExecutableField)) : Prop :=
  ∀ responseName,
    responseName ∈ left.map Prod.fst ->
      responseName ∈ right.map Prod.fst -> False

def executableFieldsMatchResponseName
    (responseName : Name) (fields : List Execution.ExecutableField) : Prop :=
  ∀ field, field ∈ fields -> field.responseName = responseName

def executableGroupWellFormed
    (group : Name × List Execution.ExecutableField) : Prop :=
  group.snd ≠ [] ∧ executableFieldsMatchResponseName group.fst group.snd

def executableGroupsWellFormed
    (groups : List (Name × List Execution.ExecutableField)) : Prop :=
  ∀ group, group ∈ groups -> executableGroupWellFormed group

def collectedResponseSelectionSet
    (responseName : Name) :
    List (Name × List Execution.ExecutableField) -> List Selection
  | [] => []
  | (groupResponseName, fields) :: rest =>
      if groupResponseName == responseName then
        Execution.mergedFieldSelectionSet fields
      else
        collectedResponseSelectionSet responseName rest

def withoutExecutableGroupsWithResponseName
    (responseName : Name)
    (groups : List (Name × List Execution.ExecutableField)) :
    List (Name × List Execution.ExecutableField) :=
  groups.filter (fun group => !(group.fst == responseName))

def executableFieldScoped? (schema : Schema)
    (field : Execution.ExecutableField) : Option FieldMerge.ScopedField := do
  let fieldDefinition <- schema.lookupField field.parentType field.fieldName
  some {
    parentType := field.parentType,
    responseName := field.responseName,
    fieldName := field.fieldName,
    arguments := field.arguments,
    outputType := fieldDefinition.outputType,
    selectionSet := field.selectionSet
  }

end GroundTypeNormalization

end NormalForm

end GraphQL
