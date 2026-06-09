import GraphQL.NormalForm.Shared.RuntimeTypes

/-!
Response-name-free structural facts shared by NormalForm proof modules.
-/
namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem selectionSetResponseNameFree_nil (schema : Schema)
    (parentType responseName : Name) :
    selectionSetResponseNameFree schema parentType responseName [] := by
  unfold selectionSetResponseNameFree
  intro selection hselection
  simp at hselection

theorem selectionSetResponseNameFree_cons {schema : Schema}
    {parentType responseName : Name} {selection : Selection}
    {selectionSet : List Selection} :
    selectionResponseNameFree schema parentType responseName selection ->
      selectionSetResponseNameFree schema parentType responseName selectionSet ->
        selectionSetResponseNameFree schema parentType responseName
          (selection :: selectionSet) := by
  unfold selectionSetResponseNameFree
  intro hselection hselectionSet candidate hcandidate
  cases hcandidate with
  | head =>
      exact hselection
  | tail _ htail =>
      exact hselectionSet candidate htail

theorem selectionSetResponseNameFree_head {schema : Schema}
    {parentType responseName : Name} {selection : Selection}
    {selectionSet : List Selection} :
    selectionSetResponseNameFree schema parentType responseName
      (selection :: selectionSet) ->
        selectionResponseNameFree schema parentType responseName selection := by
  unfold selectionSetResponseNameFree
  intro hfree
  exact hfree selection (by simp)

theorem selectionSetResponseNameFree_tail {schema : Schema}
    {parentType responseName : Name} {selection : Selection}
    {selectionSet : List Selection} :
    selectionSetResponseNameFree schema parentType responseName
      (selection :: selectionSet) ->
        selectionSetResponseNameFree schema parentType responseName selectionSet := by
  unfold selectionSetResponseNameFree
  intro hfree candidate hcandidate
  exact hfree candidate (List.mem_cons_of_mem selection hcandidate)

theorem selectionSetResponseNameFree_append {schema : Schema}
    {parentType responseName : Name} {left right : List Selection} :
    selectionSetResponseNameFree schema parentType responseName left ->
      selectionSetResponseNameFree schema parentType responseName right ->
        selectionSetResponseNameFree schema parentType responseName
          (left ++ right) := by
  unfold selectionSetResponseNameFree
  intro hleft hright selection hselection
  rcases List.mem_append.mp hselection with hselection | hselection
  · exact hleft selection hselection
  · exact hright selection hselection

theorem withoutFieldsWithResponseName_responseNameFree (schema : Schema)
    (parentType responseName : Name) :
    ∀ selectionSet,
      selectionSetResponseNameFree schema parentType responseName
        (withoutFieldsWithResponseName schema responseName selectionSet)
  | [] => by
      simpa [withoutFieldsWithResponseName] using
        selectionSetResponseNameFree_nil schema parentType responseName
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [withoutFieldsWithResponseName, hname]
            exact withoutFieldsWithResponseName_responseNameFree schema
              parentType responseName rest
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldsWithResponseName, hfalse]
            apply selectionSetResponseNameFree_cons
            · simp [selectionResponseNameFree]
              intro heq
              subst fieldResponseName
              simp at hfalse
            · exact withoutFieldsWithResponseName_responseNameFree schema
                parentType responseName rest
      | inlineFragment typeCondition directives selectionSet =>
          simp [withoutFieldsWithResponseName]
          apply selectionSetResponseNameFree_cons
          · cases typeCondition with
            | none =>
                simpa [selectionResponseNameFree] using
                  withoutFieldsWithResponseName_responseNameFree schema
                    parentType responseName selectionSet
            | some typeCondition =>
                simp [selectionResponseNameFree]
                intro _hoverlap
                exact withoutFieldsWithResponseName_responseNameFree schema
                  parentType responseName selectionSet
          · exact withoutFieldsWithResponseName_responseNameFree schema
              parentType responseName rest

theorem withoutFieldsWithResponseName_preserves_responseNameFree
    (schema : Schema) (removedResponseName : Name)
    (parentType responseName : Name) :
    ∀ selectionSet,
      selectionSetResponseNameFree schema parentType responseName selectionSet ->
        selectionSetResponseNameFree schema parentType responseName
          (withoutFieldsWithResponseName schema removedResponseName selectionSet)
  | [], hfree => by
      simpa [withoutFieldsWithResponseName] using hfree
  | selection :: rest, hfree => by
      have hselection := selectionSetResponseNameFree_head hfree
      have hrest := selectionSetResponseNameFree_tail hfree
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == removedResponseName) = true
          · simp [withoutFieldsWithResponseName, hname]
            exact withoutFieldsWithResponseName_preserves_responseNameFree
              schema removedResponseName parentType responseName rest hrest
          · have hfalse : (fieldResponseName == removedResponseName) = false := by
              cases hmatch : fieldResponseName == removedResponseName
              · rfl
              · contradiction
            simp [withoutFieldsWithResponseName, hfalse]
            exact selectionSetResponseNameFree_cons hselection
              (withoutFieldsWithResponseName_preserves_responseNameFree
                schema removedResponseName parentType responseName rest hrest)
      | inlineFragment typeCondition directives selectionSet =>
          simp [withoutFieldsWithResponseName]
          apply selectionSetResponseNameFree_cons
          · cases typeCondition with
            | none =>
                have hselectionSet :
                    selectionSetResponseNameFree schema parentType responseName
                      selectionSet := by
                  simpa [selectionResponseNameFree] using hselection
                simpa [selectionResponseNameFree] using
                  withoutFieldsWithResponseName_preserves_responseNameFree
                    schema removedResponseName parentType responseName
                    selectionSet hselectionSet
            | some typeCondition =>
                have hselectionSet :
                    schema.typesOverlapBool parentType typeCondition = true ->
                      selectionSetResponseNameFree schema parentType responseName
                        selectionSet := by
                  simpa [selectionResponseNameFree] using hselection
                simp [selectionResponseNameFree]
                intro hoverlap
                exact withoutFieldsWithResponseName_preserves_responseNameFree
                  schema removedResponseName parentType responseName
                  selectionSet (hselectionSet hoverlap)
          · exact withoutFieldsWithResponseName_preserves_responseNameFree
              schema removedResponseName parentType responseName rest hrest

end GroundTypeNormalization

end NormalForm

end GraphQL
