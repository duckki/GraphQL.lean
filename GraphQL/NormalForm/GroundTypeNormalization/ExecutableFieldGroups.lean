import GraphQL.NormalForm
import GraphQL.Execution
import GraphQL.Validation.FieldMerge

/-!
Executable field-group invariants used by ground-type normalization proofs.
-/
namespace GraphQL

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
