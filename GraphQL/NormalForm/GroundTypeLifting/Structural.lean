import GraphQL.NormalForm.Shared.ResponseNameFree

/-!
Structural ground-type lifting facts shared by the semantic proof modules.
-/
namespace GraphQL

namespace NormalForm

namespace GroundTypeLifting

variable {ObjectIdentity : Type}

mutual
  theorem groundLiftSelection_directiveFree
      (schema : Schema) (parentType : Name) :
      ∀ selection,
        selectionDirectiveFree selection ->
          selectionDirectiveFree
            (groundLiftSelection schema parentType selection)
    | .field responseName fieldName arguments directives selectionSet,
      hfree => by
        have hdirectives : directives = [] := hfree.1
        have hselectionFree : selectionSetDirectiveFree selectionSet := hfree.2
        subst directives
        cases hlookup : schema.lookupField parentType fieldName with
        | none =>
            simp [groundLiftSelection, hlookup]
            exact ⟨rfl, groundLiftSelectionSet_directiveFree schema
              parentType selectionSet hselectionFree⟩
        | some fieldDefinition =>
            by_cases hleaf :
                leafTypeNameBool schema
                  fieldDefinition.outputType.namedType = true
            · simp [groundLiftSelection, hlookup, hleaf,
                selectionDirectiveFree, selectionSetDirectiveFree]
            · have hleafFalse :
                  leafTypeNameBool schema
                    fieldDefinition.outputType.namedType = false := by
                cases hmatch :
                    leafTypeNameBool schema
                      fieldDefinition.outputType.namedType
                · rfl
                · exact False.elim (hleaf hmatch)
              by_cases hobject :
                  objectTypeNameBool schema
                    fieldDefinition.outputType.namedType = true
              · simp [groundLiftSelection, hlookup, hleafFalse, hobject]
                exact ⟨rfl, groundLiftSelectionSet_directiveFree schema
                  fieldDefinition.outputType.namedType selectionSet
                  hselectionFree⟩
              · have hobjectFalse :
                    objectTypeNameBool schema
                      fieldDefinition.outputType.namedType = false := by
                  cases hmatch :
                      objectTypeNameBool schema
                        fieldDefinition.outputType.namedType
                  · rfl
                  · exact False.elim (hobject hmatch)
                simp [groundLiftSelection, hlookup, hleafFalse, hobjectFalse]
                let branches :=
                  groundObjectTypesForType schema
                    fieldDefinition.outputType.namedType
                constructor
                · rfl
                · change selectionSetDirectiveFree
                    (branches.map
                      (fun objectType =>
                        Selection.inlineFragment (some objectType) []
                          (groundLiftSelectionSet schema objectType
                            selectionSet)))
                  induction branches with
                  | nil =>
                      simp [selectionSetDirectiveFree]
                  | cons objectType rest ih =>
                      exact ⟨
                        ⟨rfl, groundLiftSelectionSet_directiveFree schema
                          objectType selectionSet hselectionFree⟩,
                        ih⟩
    | .inlineFragment none directives selectionSet, hfree => by
        have hdirectives : directives = [] := hfree.1
        have hselectionFree : selectionSetDirectiveFree selectionSet := hfree.2
        subst directives
        exact ⟨rfl, groundLiftSelectionSet_directiveFree schema parentType
          selectionSet hselectionFree⟩
    | .inlineFragment (some typeCondition) directives selectionSet, hfree => by
        have hdirectives : directives = [] := hfree.1
        have hselectionFree : selectionSetDirectiveFree selectionSet := hfree.2
        subst directives
        exact ⟨rfl, groundLiftSelectionSet_directiveFree schema typeCondition
          selectionSet hselectionFree⟩

  theorem groundLiftSelectionSet_directiveFree
      (schema : Schema) (parentType : Name) :
      ∀ selectionSet,
        selectionSetDirectiveFree selectionSet ->
          selectionSetDirectiveFree
            (groundLiftSelectionSet schema parentType selectionSet)
    | [], _hfree => by
        simp [groundLiftSelectionSet, selectionSetDirectiveFree]
    | selection :: rest, hfree => by
        exact ⟨
          groundLiftSelection_directiveFree schema parentType selection
            (selectionSetDirectiveFree_head hfree),
          groundLiftSelectionSet_directiveFree schema parentType rest
            (selectionSetDirectiveFree_tail hfree)⟩
end

mutual
  theorem groundLiftSelection_responseNameFree
      (schema : Schema) (responseScope responseName liftParent : Name) :
      ∀ selection,
        selectionResponseNameFree schema responseScope responseName selection ->
          selectionResponseNameFree schema responseScope responseName
            (groundLiftSelection schema liftParent selection)
    | .field fieldResponseName fieldName arguments directives selectionSet,
        hfree => by
        cases hlookup : schema.lookupField liftParent fieldName <;>
          simpa [groundLiftSelection, hlookup, selectionResponseNameFree]
            using hfree
    | .inlineFragment none directives selectionSet, hfree => by
        have hchild :
            selectionSetResponseNameFree schema responseScope responseName
              selectionSet := by
          simpa [selectionResponseNameFree] using hfree
        simpa [groundLiftSelection, selectionResponseNameFree] using
          groundLiftSelectionSet_responseNameFree schema responseScope
            responseName liftParent selectionSet hchild
    | .inlineFragment (some typeCondition) directives selectionSet, hfree => by
        have hchild :
            schema.typesOverlapBool responseScope typeCondition = true ->
              selectionSetResponseNameFree schema responseScope responseName
                selectionSet := by
          simpa [selectionResponseNameFree] using hfree
        simp [groundLiftSelection, selectionResponseNameFree]
        intro hoverlap
        exact
          groundLiftSelectionSet_responseNameFree schema responseScope
            responseName typeCondition selectionSet (hchild hoverlap)

  theorem groundLiftSelectionSet_responseNameFree
      (schema : Schema) (responseScope responseName liftParent : Name) :
      ∀ selectionSet,
        selectionSetResponseNameFree schema responseScope responseName
          selectionSet ->
          selectionSetResponseNameFree schema responseScope responseName
            (groundLiftSelectionSet schema liftParent selectionSet)
    | [], _hfree => by
        exact selectionSetResponseNameFree_nil schema responseScope
          responseName
    | selection :: rest, hfree => by
        exact selectionSetResponseNameFree_cons
          (groundLiftSelection_responseNameFree schema responseScope
            responseName liftParent selection
            (selectionSetResponseNameFree_head hfree))
          (groundLiftSelectionSet_responseNameFree schema responseScope
            responseName liftParent rest
            (selectionSetResponseNameFree_tail hfree))
end

theorem withoutFieldsWithResponseName_groundLiftSelectionSet
      (schema : Schema) (responseName parentType : Name) :
      ∀ selectionSet,
        withoutFieldsWithResponseName schema responseName
            (groundLiftSelectionSet schema parentType selectionSet)
          =
        groundLiftSelectionSet schema parentType
          (withoutFieldsWithResponseName schema responseName selectionSet)
    | [] => by
        simp [groundLiftSelectionSet, withoutFieldsWithResponseName]
    | selection :: rest => by
        rw [groundLiftSelectionSet]
        cases selection with
        | field fieldResponseName fieldName arguments directives selectionSet =>
            by_cases hresponse : (fieldResponseName == responseName) = true
            · have heq : fieldResponseName = responseName :=
                beq_iff_eq.mp hresponse
              subst fieldResponseName
              cases hlookup : schema.lookupField parentType fieldName <;>
                simp [groundLiftSelection, withoutFieldsWithResponseName,
                  hlookup,
                  withoutFieldsWithResponseName_groundLiftSelectionSet schema
                    responseName parentType rest]
            · have hfalse : (fieldResponseName == responseName) = false := by
                cases hmatch : fieldResponseName == responseName
                · rfl
                · exact False.elim (hresponse hmatch)
              have hne : fieldResponseName ≠ responseName := by
                intro heq
                subst fieldResponseName
                simp at hfalse
              cases hlookup : schema.lookupField parentType fieldName <;>
                simp [groundLiftSelection, withoutFieldsWithResponseName,
                  hlookup, hfalse, groundLiftSelectionSet,
                  withoutFieldsWithResponseName_groundLiftSelectionSet schema
                    responseName parentType rest]
        | inlineFragment typeCondition directives selectionSet =>
            cases typeCondition with
            | none =>
                simp [groundLiftSelection, withoutFieldsWithResponseName,
                  groundLiftSelectionSet,
                  withoutFieldsWithResponseName_groundLiftSelectionSet schema
                    responseName parentType selectionSet,
                  withoutFieldsWithResponseName_groundLiftSelectionSet schema
                    responseName parentType rest]
            | some typeCondition =>
                simp [groundLiftSelection, withoutFieldsWithResponseName,
                  groundLiftSelectionSet,
                  withoutFieldsWithResponseName_groundLiftSelectionSet schema
                    responseName typeCondition selectionSet,
                  withoutFieldsWithResponseName_groundLiftSelectionSet schema
                    responseName parentType rest]

theorem groundLiftSelectionSet_append
    (schema : Schema) (parentType : Name) :
    ∀ left right : List Selection,
      groundLiftSelectionSet schema parentType (left ++ right)
        =
      groundLiftSelectionSet schema parentType left
        ++ groundLiftSelectionSet schema parentType right
  | [], right => by
      simp [groundLiftSelectionSet]
  | selection :: rest, right => by
      simp [groundLiftSelectionSet, groundLiftSelectionSet_append schema
        parentType rest right]


end GroundTypeLifting

end NormalForm

end GraphQL
