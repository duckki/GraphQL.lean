import GraphQL.Algorithms.ExecutionUngrouped.Semantics
import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Collection
import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.GroupList
import GraphQL.DataModel
import GraphQL.DataModel.ArgumentEquivalence
import GraphQL.DataModel.StoreResolverStability
import GraphQL.NormalForm.CompleteNormalization.Validity.Operation

/-!
Store-backed wrappers for ungrouped execution.

The closed derivation of the recursive/global invariants is intentionally kept out
of this thin bridge.  This module connects those invariant assumptions to the
complete-normalization preservation theorem over the current store-backed resolver
model.
-/
namespace GraphQL

namespace Algorithms

namespace ExecutionUngrouped

open GraphQL.Execution

abbrev RecursiveErrorNeutralFor
    {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection) : Prop :=
  ∀ responseName field fields prefixTail later,
    (responseName, field :: fields) ∈
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet ->
    (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
    later ∈ fields ->
    ∀ childDepth runtimeType (identity : ObjectRef),
      childDepth < depth ->
        VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
          runtimeType (.object runtimeType identity) later.selectionSet
          (visitSubfields schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))
            (.object [])).fst

-- Store-backed ungrouped execution as a full GraphQL response.
def executeOperationResponseAtDepth
    (schema : Schema) (store : GraphQL.DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) : Response :=
  executeQueryAtDepth schema (store.resolvers schema) variableValues
    operation depth store.rootExecutionValue

-- Spec store-backed execution as a full GraphQL response.
def specExecuteOperationAtDepth
    (schema : Schema) (store : GraphQL.DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) : Response :=
  GraphQL.DataModel.executeOperationAtDepth schema store variableValues
    operation depth

-- Store-backed ungrouped execution, kept as a data projection helper for the
-- existing normalization proof stack.
def executeOperationAtDepth (schema : Schema) (store : GraphQL.DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) : ResponseValue :=
  (executeOperationResponseAtDepth schema store variableValues operation depth).data

-- Data projection of spec store-backed execution used by ungrouped data-equivalence
-- compatibility theorems.
def specExecuteOperationDataAtDepth (schema : Schema)
    (store : GraphQL.DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) : ResponseValue :=
  (specExecuteOperationAtDepth schema store variableValues operation depth).data

-- Store-backed ungrouped execution with the operation-derived depth bound, as a
-- full GraphQL response.
def executeOperationResponse
    (schema : Schema) (store : GraphQL.DataModel.Store)
    (variableValues : VariableValues) (operation : Operation) : Response :=
  executeQuery schema (store.resolvers schema) variableValues operation
    store.rootExecutionValue

-- Data projection of store-backed ungrouped execution with the operation-derived
-- depth bound.
def executeOperation (schema : Schema) (store : GraphQL.DataModel.Store)
    (variableValues : VariableValues) (operation : Operation) : ResponseValue :=
  (executeOperationResponse schema store variableValues operation).data


end ExecutionUngrouped

end Algorithms

end GraphQL
