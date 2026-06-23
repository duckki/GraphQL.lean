import GraphQL.NormalForm.GroundTypeNormalization.RuntimeFragmentSemantics

/-!
Operation-level semantic wrapper facts for the alternative ground-lift phase.

This file keeps the resolver-parametric operation wrapper: a caller that proves
selection-set preservation for the lifted root obtains query-level preservation.
-/
namespace GraphQL

namespace NormalForm

namespace GroundTypeLifting

variable {ObjectRef : Type}

theorem rootSourceAppliesBool_groundLiftOperation
    (schema : Schema) (operation : Operation)
    (source : Execution.ResolverValue ObjectRef) :
    Execution.rootSourceAppliesBool schema
        (groundLiftOperation schema operation) source =
      Execution.rootSourceAppliesBool schema operation source := by
  rfl

theorem executeQueryAtDepth_groundLiftOperation_eq_of_selectionSet
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (depth : Nat)
    (source : Execution.ResolverValue ObjectRef) :
    (∀ runtimeType ref,
      source = Execution.ResolverValue.object runtimeType ref ->
      schema.typeIncludesObjectBool operation.rootType runtimeType = true ->
        Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (groundLiftSelectionSet schema operation.rootType
            operation.selectionSet)
        =
        Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source operation.selectionSet) ->
      Execution.executeQueryAtDepth schema resolvers variableValues
        (groundLiftOperation schema operation) depth source
      =
      Execution.executeQueryAtDepth schema resolvers variableValues
        operation depth source := by
  intro hselection
  rw [Execution.executeQueryAtDepth]
  rw [rootSourceAppliesBool_groundLiftOperation]
  rw [Execution.executeQueryAtDepth]
  cases hroot :
      Execution.rootSourceAppliesBool schema operation source
  · simp
  · rcases
      GroundTypeNormalization.rootSourceAppliesBool_true_object
        schema operation source hroot with
      ⟨runtimeType, ref, hsource, hinclude⟩
    simp [groundLiftOperation]
    exact congrArg
      (fun (completed : Execution.Result (List (Name × Execution.ResponseValue))) =>
        match completed with
        | Except.error errors =>
            ({ data := Execution.ResponseValue.null, errors := errors } :
              Execution.Response)
        | Except.ok (fields, errors) =>
            ({ data := Execution.ResponseValue.object fields, errors := errors } :
              Execution.Response))
      (by
        simpa [Execution.executeSelectionSet] using
          hselection runtimeType ref hsource hinclude)

end GroundTypeLifting

end NormalForm

end GraphQL
