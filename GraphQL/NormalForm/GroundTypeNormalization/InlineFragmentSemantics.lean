import GraphQL.NormalForm.GroundTypeNormalization.RuntimeFragmentSemantics

/-!
Inline-fragment semantic cases for ground-type normalization.
-/
namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

variable {ObjectIdentity : Type}

theorem normalizeSelectionSet_executeSelectionSet_inlineFragment_some_noOverlap_case
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType typeCondition : Name)
    (source : Execution.Value ObjectIdentity)
    (selectionSet rest : List Selection) :
    (∃ runtimeType identity,
      source = .object runtimeType identity
        ∧ schema.typeIncludesObjectBool parentType runtimeType = true) ->
      schema.typesOverlapBool parentType typeCondition = false ->
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source
          (normalizeSelectionSet schema parentType rest)
          =
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source rest ->
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType
              (Selection.inlineFragment (some typeCondition) [] selectionSet
                :: rest))
            =
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (Selection.inlineFragment (some typeCondition) [] selectionSet
              :: rest) := by
  intro hsource hoverlap hrest
  have happly :
      Execution.doesFragmentTypeApplyBool schema parentType source
        typeCondition = false :=
    doesFragmentTypeApplyBool_false_of_typesOverlapBool_false_of_source
      schema hsource hoverlap
  simp [normalizeSelectionSet, hoverlap]
  rw [hrest]
  exact (executeSelectionSet_inlineFragment_some_directiveFree_skip schema
    resolvers variableValues depth parentType typeCondition source
    selectionSet rest happly).symm

theorem normalizeSelectionSet_executeSelectionSet_inlineFragment_none_case
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectIdentity)
    (selectionSet rest : List Selection) :
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source
      (normalizeSelectionSet schema parentType (selectionSet ++ rest))
      =
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source (selectionSet ++ rest) ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (normalizeSelectionSet schema parentType
          (Selection.inlineFragment none [] selectionSet :: rest))
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (Selection.inlineFragment none [] selectionSet :: rest) := by
  intro happend
  simp [normalizeSelectionSet]
  rw [happend]
  exact (executeSelectionSet_inlineFragment_none_directiveFree_flatten schema
    resolvers variableValues depth parentType source selectionSet rest).symm

theorem normalizeSelectionSet_executeSelectionSet_inlineFragment_some_apply_case
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType typeCondition : Name)
    (source : Execution.Value ObjectIdentity)
    (selectionSet rest : List Selection) :
    schema.typesOverlapBool parentType typeCondition = true ->
      Execution.doesFragmentTypeApplyBool schema parentType source
        typeCondition = true ->
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source
          (normalizeSelectionSet schema parentType (selectionSet ++ rest))
          =
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source (selectionSet ++ rest) ->
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType
              (Selection.inlineFragment (some typeCondition) [] selectionSet
                :: rest))
            =
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (Selection.inlineFragment (some typeCondition) [] selectionSet
              :: rest) := by
  intro hoverlap happly happend
  simp [normalizeSelectionSet, hoverlap]
  rw [happend]
  exact (executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
    schema resolvers variableValues depth parentType typeCondition source
    selectionSet rest happly).symm

theorem normalizeSelectionSet_executeSelectionSet_inlineFragment_some_overlap_case
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType typeCondition : Name)
    (source : Execution.Value ObjectIdentity)
    (selectionSet rest : List Selection) :
    objectTypeNameBool schema parentType = true ->
      (∃ runtimeType identity,
        source = .object runtimeType identity
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true) ->
        schema.typesOverlapBool parentType typeCondition = true ->
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType (selectionSet ++ rest))
            =
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source (selectionSet ++ rest) ->
            Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source
              (normalizeSelectionSet schema parentType
                (Selection.inlineFragment (some typeCondition) [] selectionSet
                  :: rest))
              =
            Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source
              (Selection.inlineFragment (some typeCondition) [] selectionSet
                :: rest) := by
  intro hobject hsource hoverlap happend
  exact normalizeSelectionSet_executeSelectionSet_inlineFragment_some_apply_case
    schema resolvers variableValues depth parentType typeCondition source
    selectionSet rest hoverlap
    (doesFragmentTypeApplyBool_true_of_typesOverlapBool_true_of_object_source
      schema hobject hsource hoverlap)
    happend


end GroundTypeNormalization

end NormalForm

end GraphQL
