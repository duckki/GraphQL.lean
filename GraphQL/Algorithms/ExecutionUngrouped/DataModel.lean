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

-- Store-backed ungrouped execution, mirroring `GraphQL.DataModel.executeOperationAtDepth`.
def executeOperationAtDepth (schema : Schema) (store : GraphQL.DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) : Response :=
  executeQueryAtDepth schema (store.resolvers schema) variableValues
    operation depth store.rootExecutionValue

-- Store-backed ungrouped execution with the operation-derived depth bound.
def executeOperation (schema : Schema) (store : GraphQL.DataModel.Store)
    (variableValues : VariableValues) (operation : Operation) : Response :=
  executeQuery schema (store.resolvers schema) variableValues operation
    store.rootExecutionValue

theorem typeIncludesObjectBool_eq_true_of_typeIncludesObject
    (schema : Schema) {typeName runtimeType : Name} :
    schema.typeIncludesObject typeName runtimeType ->
      schema.typeIncludesObjectBool typeName runtimeType = true := by
  intro hinclude
  simpa [Schema.typeIncludesObject, Schema.typeIncludesObjectBool] using
    hinclude

theorem rootSourceAppliesBool_store_rootExecutionValue
    (schema : Schema) (store : DataModel.Store) (operation : Operation) :
    store.wellTyped schema ->
    Validation.operationDefinitionValid schema operation ->
      rootSourceAppliesBool schema operation store.rootExecutionValue = true := by
  intro hstore hvalid
  have hrootType : operation.rootType = schema.queryType :=
    Validation.operationDefinitionValid_rootType_eq hvalid
  have hinclude : schema.typeIncludesObject schema.queryType store.root.typeName :=
    hstore.1
  simpa [DataModel.Store.rootExecutionValue, rootSourceAppliesBool,
    runtimeObjectType?, hrootType] using
    typeIncludesObjectBool_eq_true_of_typeIncludesObject schema hinclude

theorem store_resolversRespectValidFieldAndArgumentEquivalence
    (schema : Schema) (store : DataModel.Store)
    (source : Value DataModel.ObjectRef) :
    ResolversRespectValidFieldAndArgumentEquivalence
      (store.resolvers schema) source := by
  intro firstParent laterParent fieldName firstArguments laterArguments
    hfirstNodup hlaterNodup hequivalent
  exact
    DataModel.Store.resolvers_eq_of_argumentsEqBool schema store firstParent
      laterParent fieldName source
      (DataModel.Argument.fieldAccessEqBool_of_argumentsEquivalent_names_nodup_valid
        DataModel.Argument.fieldAccessEqBool_of_validEquivalentAlignment
        firstArguments laterArguments hfirstNodup hlaterNodup hequivalent)

theorem executionValidFieldSemanticStateInvariant_store_root
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    Validation.operationDefinitionValid schema operation ->
      ExecutionValidFieldSemanticStateInvariant
        { window :=
          { schema := schema
            resolvers := store.resolvers schema
            variableValues := variableValues
            depth := depth
            parentType := operation.rootType
            source := store.rootExecutionValue
            selectionSet := operation.selectionSet }
          initial := .object [] } := by
  intro hstore hvalid
  have hroot :
      rootSourceAppliesBool schema operation
          (Execution.Value.object store.root.typeName
            (some (DataModel.objectRefOfId store.root.id))) =
        true := by
    simpa [DataModel.Store.rootExecutionValue] using
      rootSourceAppliesBool_store_rootExecutionValue schema store operation
        hstore hvalid
  simpa [DataModel.Store.rootExecutionValue] using
    ExecutionValidFieldSemanticStateInvariant.of_valid_root_operation_canMerge
      schema (store.resolvers schema) variableValues depth operation
      store.root.typeName (DataModel.objectRefOfId store.root.id)
      (Execution.Response.object []) hroot hvalid
      (store_resolversRespectValidFieldAndArgumentEquivalence schema store
        (Execution.Value.object store.root.typeName
          (some (DataModel.objectRefOfId store.root.id))))

theorem executionCollectedFieldInvariant_store_root
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    Validation.operationDefinitionValid schema operation ->
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := store.resolvers schema
            variableValues := variableValues
            depth := depth
            parentType := operation.rootType
            source := store.rootExecutionValue
            selectionSet := operation.selectionSet }
          initial := .object [] } := by
  intro hstore hvalid
  exact
    ExecutionCollectedFieldInvariant.of_validFieldSemantic
      { window :=
        { schema := schema
          resolvers := store.resolvers schema
          variableValues := variableValues
          depth := depth
          parentType := operation.rootType
          source := store.rootExecutionValue
          selectionSet := operation.selectionSet }
        initial := .object [] }
      (executionValidFieldSemanticStateInvariant_store_root schema store
        variableValues operation depth hstore hvalid)

theorem collectedGroupsFieldValidationMergeCompatible_store_root
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    Validation.operationDefinitionValid schema operation ->
      CollectedGroupsFieldValidationMergeCompatible
        (GraphQL.Execution.collectFields schema variableValues operation.rootType
          store.rootExecutionValue operation.selectionSet) := by
  intro hstore hvalid
  exact
    (executionValidFieldSemanticStateInvariant_store_root schema store
      variableValues operation depth hstore hvalid).groupedFieldsFieldCompatible

def selectionSetLocalInvariants_store_root
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    Validation.operationDefinitionValid schema operation ->
    VisitSubfieldsFlatCollects schema (store.resolvers schema) variableValues
      (depth + 1) operation.rootType store.rootExecutionValue
      operation.selectionSet (.object []) ->
    SelectionSetLocalInvariants schema (store.resolvers schema)
      variableValues depth operation.rootType store.rootExecutionValue
      operation.selectionSet := by
  intro hstore hvalid flat
  exact
    { flat := flat
      collected :=
        executionCollectedFieldInvariant_store_root schema store variableValues
          operation depth hstore hvalid
      compatible :=
        collectedGroupsFieldValidationMergeCompatible_store_root schema store
          variableValues operation depth hstore hvalid }

theorem executionValidFieldSemanticStateInvariant_store_object_selectionSet_canMerge
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : Option DataModel.ObjectRef)
    (selectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    ScopedParentRuntimeApplies schema runtimeType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
      ExecutionValidFieldSemanticStateInvariant
        { window :=
          { schema := schema
            resolvers := store.resolvers schema
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := .object runtimeType identity
            selectionSet := selectionSet }
          initial := .object [] } := by
  intro hparentRuntime hvalid hmerge
  exact
    ExecutionValidFieldSemanticStateInvariant.of_valid_object_selectionSet_canMerge_optional
      schema (store.resolvers schema) variableValues depth parentType
      runtimeType identity selectionSet (Execution.Response.object [])
      variableDefinitions hparentRuntime hvalid hmerge
      (store_resolversRespectValidFieldAndArgumentEquivalence schema store
        (Execution.Value.object runtimeType identity))

theorem executionCollectedFieldInvariant_store_object_selectionSet_canMerge
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : Option DataModel.ObjectRef)
    (selectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    ScopedParentRuntimeApplies schema runtimeType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := store.resolvers schema
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := .object runtimeType identity
            selectionSet := selectionSet }
          initial := .object [] } := by
  intro hparentRuntime hvalid hmerge
  exact
    ExecutionCollectedFieldInvariant.of_validFieldSemantic
      { window :=
        { schema := schema
          resolvers := store.resolvers schema
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := .object runtimeType identity
          selectionSet := selectionSet }
        initial := .object [] }
      (executionValidFieldSemanticStateInvariant_store_object_selectionSet_canMerge
        schema store variableValues depth parentType runtimeType identity
        selectionSet variableDefinitions hparentRuntime hvalid hmerge)

theorem collectedGroupsFieldValidationMergeCompatible_store_object_selectionSet_canMerge
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : Option DataModel.ObjectRef)
    (selectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    ScopedParentRuntimeApplies schema runtimeType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
      CollectedGroupsFieldValidationMergeCompatible
        (GraphQL.Execution.collectFields schema variableValues parentType
          (.object runtimeType identity) selectionSet) := by
  intro hparentRuntime hvalid hmerge
  exact
    (executionValidFieldSemanticStateInvariant_store_object_selectionSet_canMerge
      schema store variableValues depth parentType runtimeType identity
      selectionSet variableDefinitions hparentRuntime hvalid hmerge).groupedFieldsFieldCompatible

theorem executionCollectedFieldInvariant_store_object_of_groupedFacts
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : Option DataModel.ObjectRef)
    (selectionSet : List Selection) :
    CollectedGroupsFieldValidationMergeCompatible
      (GraphQL.Execution.collectFields schema variableValues parentType
        (.object runtimeType identity) selectionSet) ->
    CollectedGroupsArgumentsNodup
      (GraphQL.Execution.collectFields schema variableValues parentType
        (.object runtimeType identity) selectionSet) ->
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := store.resolvers schema
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := .object runtimeType identity
            selectionSet := selectionSet }
          initial := .object [] } := by
  intro hcompatible hargumentsNodup
  constructor
  · exact collectFields_pairKeysNodup schema variableValues parentType
      (.object runtimeType identity) selectionSet
  · exact
      CollectedGroupsFieldValidationMergeCompatible.resolveStableValid
        (store.resolvers schema) (.object runtimeType identity)
        (GraphQL.Execution.collectFields schema variableValues parentType
          (.object runtimeType identity) selectionSet)
        (store_resolversRespectValidFieldAndArgumentEquivalence schema store
          (.object runtimeType identity))
        hcompatible hargumentsNodup

def selectionSetLocalInvariants_store_object_selectionSet_canMerge
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : Option DataModel.ObjectRef)
    (selectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    VisitSubfieldsFlatCollects schema (store.resolvers schema) variableValues
      (depth + 1) parentType (.object runtimeType identity) selectionSet
      (.object []) ->
    ScopedParentRuntimeApplies schema runtimeType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
    SelectionSetLocalInvariants schema (store.resolvers schema)
      variableValues depth parentType (.object runtimeType identity)
      selectionSet := by
  intro flat hparentRuntime hvalid hmerge
  exact
    { flat := flat
      collected :=
        executionCollectedFieldInvariant_store_object_selectionSet_canMerge
          schema store variableValues depth parentType runtimeType identity
          selectionSet variableDefinitions hparentRuntime hvalid hmerge
      compatible :=
        collectedGroupsFieldValidationMergeCompatible_store_object_selectionSet_canMerge
          schema store variableValues depth parentType runtimeType identity
          selectionSet variableDefinitions hparentRuntime hvalid hmerge }

def selectionSetLocalInvariants_store_object_of_groupedFacts
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : Option DataModel.ObjectRef)
    (selectionSet : List Selection) :
    VisitSubfieldsFlatCollects schema (store.resolvers schema) variableValues
      (depth + 1) parentType (.object runtimeType identity) selectionSet
      (.object []) ->
    CollectedGroupsFieldValidationMergeCompatible
      (GraphQL.Execution.collectFields schema variableValues parentType
        (.object runtimeType identity) selectionSet) ->
    CollectedGroupsArgumentsNodup
      (GraphQL.Execution.collectFields schema variableValues parentType
        (.object runtimeType identity) selectionSet) ->
    SelectionSetLocalInvariants schema (store.resolvers schema)
      variableValues depth parentType (.object runtimeType identity)
      selectionSet := by
  intro flat hcompatible hargumentsNodup
  exact
    { flat := flat
      collected :=
        executionCollectedFieldInvariant_store_object_of_groupedFacts
          schema store variableValues depth parentType runtimeType identity
          selectionSet hcompatible hargumentsNodup
      compatible := hcompatible }

def selectionSetLocalInvariants_store_object_of_implementationValid
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (collectParent validParent runtimeType : Name)
    (identity : Option DataModel.ObjectRef)
    (selectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    VisitSubfieldsFlatCollects schema (store.resolvers schema) variableValues
      (depth + 1) collectParent (.object runtimeType identity) selectionSet
      (.object []) ->
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    NormalForm.selectionSetLookupValid schema validParent selectionSet ->
    Validation.selectionSetImplementationValidInScope schema variableDefinitions
      validParent selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
    SelectionSetLocalInvariants schema (store.resolvers schema)
      variableValues depth collectParent (.object runtimeType identity)
      selectionSet := by
  intro flat hparentRuntime hlookupValid himplementation hmerge
  exact
    selectionSetLocalInvariants_store_object_of_groupedFacts
      schema store variableValues depth collectParent runtimeType identity
      selectionSet flat
      (collectFields_fieldCompatible_of_canMerge_lookupValid_object schema
        variableValues collectParent validParent runtimeType identity
        selectionSet hmerge hparentRuntime hlookupValid)
      (collectFields_argumentsNodup_of_selectionSetImplementationValidInScope_object
        schema variableDefinitions variableValues collectParent validParent
        runtimeType identity selectionSet hparentRuntime himplementation)

def selectionSetLocalFreshPrefixInvariants_store_object_selectionSet_canMerge
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : Option DataModel.ObjectRef)
    (selectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    FreshPrefixSelectionDerivation schema variableValues parentType
      (.object runtimeType identity) selectionSet ->
    ScopedParentRuntimeApplies schema runtimeType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
      SelectionSetLocalFreshPrefixInvariants schema (store.resolvers schema)
        variableValues depth parentType (.object runtimeType identity)
        selectionSet := by
  intro derivation hparentRuntime hvalid hmerge
  exact
    SelectionSetLocalFreshPrefixInvariants.of_freshPrefixDerivation
      derivation
      (executionCollectedFieldInvariant_store_object_selectionSet_canMerge
        schema store variableValues depth parentType runtimeType identity
        selectionSet variableDefinitions hparentRuntime hvalid hmerge)
      (collectedGroupsFieldValidationMergeCompatible_store_object_selectionSet_canMerge
        schema store variableValues depth parentType runtimeType identity
        selectionSet variableDefinitions hparentRuntime hvalid hmerge)

def recursiveGroupedSelectionSetState_store_object_selectionSet_canMerge_of_flat
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : Option DataModel.ObjectRef)
    (selectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    VisitSubfieldsFlatCollects schema (store.resolvers schema) variableValues
      (depth + 1) parentType (.object runtimeType identity) selectionSet
      (.object []) ->
    ScopedParentRuntimeApplies schema runtimeType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues parentType
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth childRuntime (childIdentity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          childRuntime = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth childRuntime
          (.object childRuntime childIdentity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth parentType (.object runtimeType identity)
        selectionSet := by
  intro flat hparentRuntime hvalid hmerge hchildren
  exact
    RecursiveGroupedSelectionSetState.of_localInvariants
      (selectionSetLocalInvariants_store_object_selectionSet_canMerge
        schema store variableValues depth parentType runtimeType identity
        selectionSet variableDefinitions flat hparentRuntime hvalid hmerge)
      hchildren

def recursiveGroupedSelectionSetState_store_object_of_groupedFacts
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : Option DataModel.ObjectRef)
    (selectionSet : List Selection) :
    VisitSubfieldsFlatCollects schema (store.resolvers schema) variableValues
      (depth + 1) parentType (.object runtimeType identity) selectionSet
      (.object []) ->
    CollectedGroupsFieldValidationMergeCompatible
      (GraphQL.Execution.collectFields schema variableValues parentType
        (.object runtimeType identity) selectionSet) ->
    CollectedGroupsArgumentsNodup
      (GraphQL.Execution.collectFields schema variableValues parentType
        (.object runtimeType identity) selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues parentType
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth childRuntime (childIdentity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          childRuntime = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth childRuntime
          (.object childRuntime childIdentity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth parentType (.object runtimeType identity)
        selectionSet := by
  intro flat hcompatible hargumentsNodup hchildren
  exact
    RecursiveGroupedSelectionSetState.of_localInvariants
      (selectionSetLocalInvariants_store_object_of_groupedFacts
        schema store variableValues depth parentType runtimeType identity
        selectionSet flat hcompatible hargumentsNodup)
      hchildren

def recursiveGroupedSelectionSetState_store_object_of_implementationValid
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (collectParent validParent runtimeType : Name)
    (identity : Option DataModel.ObjectRef)
    (selectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    VisitSubfieldsFlatCollects schema (store.resolvers schema) variableValues
      (depth + 1) collectParent (.object runtimeType identity) selectionSet
      (.object []) ->
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    NormalForm.selectionSetLookupValid schema validParent selectionSet ->
    Validation.selectionSetImplementationValidInScope schema variableDefinitions
      validParent selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues collectParent
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth childRuntime (childIdentity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          childRuntime = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth childRuntime
          (.object childRuntime childIdentity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth collectParent (.object runtimeType identity)
        selectionSet := by
  intro flat hparentRuntime hlookupValid himplementation hmerge hchildren
  exact
    RecursiveGroupedSelectionSetState.of_localInvariants
      (selectionSetLocalInvariants_store_object_of_implementationValid
        schema store variableValues depth collectParent validParent runtimeType
        identity selectionSet variableDefinitions flat hparentRuntime
        hlookupValid himplementation hmerge)
      hchildren

def recursiveGroupedSelectionSetState_store_object_of_implementationValid_freshPrefixDerivation
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : Option DataModel.ObjectRef)
    (selectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    FreshPrefixSelectionDerivation schema variableValues parentType
      (.object runtimeType identity) selectionSet ->
    ScopedParentRuntimeApplies schema runtimeType parentType ->
    NormalForm.selectionSetLookupValid schema parentType selectionSet ->
    Validation.selectionSetImplementationValidInScope schema variableDefinitions
      parentType selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues parentType
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth childRuntime (childIdentity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          childRuntime = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth childRuntime
          (.object childRuntime childIdentity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth parentType (.object runtimeType identity)
        selectionSet := by
  intro derivation hparentRuntime hlookupValid himplementation hmerge
    hchildren
  have plan :
      FreshPrefixSelectionPlan schema (store.resolvers schema) variableValues
        depth parentType (.object runtimeType identity) selectionSet :=
    FreshPrefixSelectionPlan.of_derivation schema (store.resolvers schema)
      variableValues depth parentType (.object runtimeType identity) derivation
  have flat :
      VisitSubfieldsFlatCollects schema (store.resolvers schema)
        variableValues (depth + 1) parentType (.object runtimeType identity)
        selectionSet (.object []) :=
    (FreshPrefixSelectionPlan.freshFlat plan).empty
  exact
    recursiveGroupedSelectionSetState_store_object_of_implementationValid
      schema store variableValues depth parentType parentType runtimeType
      identity selectionSet variableDefinitions flat hparentRuntime hlookupValid
      himplementation hmerge hchildren

def recursiveGroupedSelectionSetState_store_object_of_generatedNormalizedFieldChild
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (childType childRuntime : Name)
    (identity : Option DataModel.ObjectRef)
    (childSelectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.typeIncludesObjectBool childType childRuntime = true ->
    generatedNormalizedFieldChild schema childType childSelectionSet ->
    NormalForm.selectionSetLookupValid schema childRuntime childSelectionSet ->
    Validation.selectionSetImplementationValidInScope schema variableDefinitions
      childRuntime childSelectionSet ->
    (∀ objectType,
      FieldMerge.fieldsInSetCanMerge schema objectType childSelectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues childRuntime
          (.object childRuntime identity) childSelectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ grandchildDepth grandchildRuntime
        (grandchildIdentity : Option DataModel.ObjectRef),
        grandchildDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          grandchildRuntime = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues grandchildDepth grandchildRuntime
          (.object grandchildRuntime grandchildIdentity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth childRuntime (.object childRuntime identity)
        childSelectionSet := by
  intro hschema hinclude hgenerated hlookupValid himplementation hmerge
    hchildren
  have hchildObject : schema.objectType childRuntime :=
    SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
      childType childRuntime (List.contains_iff_mem.mp hinclude)
  have hparentRuntime : ScopedParentRuntimeApplies schema childRuntime childRuntime :=
    NormalForm.object_typeIncludesObjectBool_self schema hchildObject
  have derivation :
      FreshPrefixSelectionDerivation schema variableValues childRuntime
        (.object childRuntime identity) childSelectionSet :=
    freshPrefixSelectionDerivation_generatedNormalizedFieldChild_runtime
      schema variableValues childType childRuntime identity childSelectionSet
      hschema hinclude hgenerated
  exact
    recursiveGroupedSelectionSetState_store_object_of_implementationValid_freshPrefixDerivation
      schema store variableValues depth childRuntime childRuntime identity
      childSelectionSet variableDefinitions derivation hparentRuntime
      hlookupValid himplementation (hmerge childRuntime) hchildren

def recursiveGroupedSelectionSetState_store_object_of_generatedNormalizedFieldChild_singletonChildren
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (childType childRuntime : Name)
    (identity : Option DataModel.ObjectRef)
    (childSelectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.typeIncludesObjectBool childType childRuntime = true ->
    generatedNormalizedFieldChild schema childType childSelectionSet ->
    NormalForm.selectionSetLookupValid schema childRuntime childSelectionSet ->
    Validation.selectionSetImplementationValidInScope schema variableDefinitions
      childRuntime childSelectionSet ->
    (∀ objectType,
      FieldMerge.fieldsInSetCanMerge schema objectType childSelectionSet) ->
    (∀ responseName field fields,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues childRuntime
          (.object childRuntime identity) childSelectionSet ->
      ∀ grandchildDepth grandchildRuntime
        (grandchildIdentity : Option DataModel.ObjectRef),
        grandchildDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          grandchildRuntime = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues grandchildDepth grandchildRuntime
          (.object grandchildRuntime grandchildIdentity)
          field.selectionSet) ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth childRuntime (.object childRuntime identity)
        childSelectionSet := by
  intro hschema hinclude hgenerated hlookupValid himplementation hmerge
    hchildren
  apply
    recursiveGroupedSelectionSetState_store_object_of_generatedNormalizedFieldChild
      schema store variableValues depth childType childRuntime identity
      childSelectionSet variableDefinitions hschema hinclude hgenerated
      hlookupValid himplementation hmerge
  intro responseName field fields prefixTail hgroup hprefix grandchildDepth
    grandchildRuntime grandchildIdentity hlt hgrandchild
  rcases
      collectFields_generatedNormalizedFieldChild_prefix_empty schema
        variableValues childType childRuntime identity childSelectionSet
        hschema hinclude hgenerated hgroup hprefix with
    ⟨_hfields, hprefixTail⟩
  subst prefixTail
  simpa using
    hchildren responseName field fields hgroup grandchildDepth
      grandchildRuntime grandchildIdentity hlt hgrandchild

def recursiveGroupedSelectionSetState_store_object_of_generatedNormalizedFieldChild_recursive
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (childType childRuntime : Name)
    (identity : Option DataModel.ObjectRef)
    (childSelectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.typeIncludesObjectBool childType childRuntime = true ->
    generatedNormalizedFieldChild schema childType childSelectionSet ->
    NormalForm.selectionSetLookupValid schema childRuntime childSelectionSet ->
    Validation.selectionSetImplementationValidInScope schema variableDefinitions
      childRuntime childSelectionSet ->
    (∀ objectType,
      FieldMerge.fieldsInSetCanMerge schema objectType childSelectionSet) ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth childRuntime (.object childRuntime identity)
        childSelectionSet := by
  intro hschema hinclude hgenerated hlookupValid himplementation hmerge
  apply
    recursiveGroupedSelectionSetState_store_object_of_generatedNormalizedFieldChild_singletonChildren
      schema store variableValues depth childType childRuntime identity
      childSelectionSet variableDefinitions hschema hinclude hgenerated
      hlookupValid himplementation hmerge
  intro responseName field fields hgroup grandchildDepth grandchildRuntime
    grandchildIdentity hlt hgrandchild
  have hgrandchildGenerated :
      generatedNormalizedFieldChild schema
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        field.selectionSet :=
    generatedNormalizedFieldChild_of_generatedNormalizedFieldChild_collectFields
      schema variableValues childType childRuntime identity childSelectionSet
      hschema hinclude hgenerated hgroup
      (prefixTail := [])
      (by
        intro candidate hcandidate
        cases hcandidate)
  rcases
      collectFields_generatedNormalizedFieldChild_childLocalFacts schema
        variableDefinitions variableValues childType childRuntime identity
        childSelectionSet responseName grandchildRuntime field fields hschema
        hinclude hgenerated hlookupValid himplementation hmerge hgroup
        hgrandchild with
    ⟨hchildLookup, hchildImplementation, hchildMerge⟩
  exact
    recursiveGroupedSelectionSetState_store_object_of_generatedNormalizedFieldChild_recursive
      schema store variableValues grandchildDepth
      ((schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName)
      grandchildRuntime grandchildIdentity field.selectionSet
      variableDefinitions hschema hgrandchild hgrandchildGenerated
      hchildLookup hchildImplementation hchildMerge
termination_by depth
decreasing_by exact Nat.lt_of_succ_lt hlt

def recursiveGroupedSelectionSetState_store_object_of_implementationValid_childLocalFacts
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (collectParent validParent runtimeType : Name)
    (identity : Option DataModel.ObjectRef)
    (selectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    SchemaWellFormedness.schemaWellFormed schema ->
    VisitSubfieldsFlatCollects schema (store.resolvers schema) variableValues
      (depth + 1) collectParent (.object runtimeType identity) selectionSet
      (.object []) ->
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    Validation.selectionSetValid schema variableDefinitions validParent
      selectionSet ->
    NormalForm.selectionSetLookupValid schema validParent selectionSet ->
    Validation.selectionSetImplementationValidInScope schema variableDefinitions
      validParent selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues collectParent
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childRuntime,
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          childRuntime = true ->
        ∀ candidate, candidate ∈ field :: prefixTail ->
          ∀ scopedField,
            scopedField ∈ FieldMerge.collectFields schema validParent
              selectionSet ->
            ScopedFieldMatchesExecutableIdentity scopedField candidate ->
            ScopedFieldRuntimeApplies schema runtimeType scopedField ->
              schema.typeIncludesObjectBool scopedField.outputType.namedType
                childRuntime = true) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues collectParent
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth childRuntime (childIdentity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          childRuntime = true ->
        NormalForm.selectionSetLookupValid schema childRuntime
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail)) ->
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions childRuntime
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail)) ->
        (∀ objectType,
          FieldMerge.fieldsInSetCanMerge schema objectType
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))) ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth childRuntime
          (.object childRuntime childIdentity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth collectParent (.object runtimeType identity)
        selectionSet := by
  intro hschema flat hparentRuntime hvalid hlookupValid himplementation hmerge
    hcompatible hchildren
  apply recursiveGroupedSelectionSetState_store_object_of_implementationValid
    schema store variableValues depth collectParent validParent runtimeType
    identity selectionSet variableDefinitions flat hparentRuntime hlookupValid
    himplementation hmerge
  intro responseName field fields prefixTail hgroup hprefix childDepth
    childRuntime childIdentity hlt hinclude
  rcases
      collectFields_group_prefix_mergedFieldSelectionSet_childLocalFacts_object
        schema variableDefinitions variableValues collectParent validParent
        runtimeType identity selectionSet responseName childRuntime field fields
        prefixTail hschema hparentRuntime hvalid hlookupValid himplementation
        hmerge hgroup hprefix
        (hcompatible responseName field fields prefixTail hgroup hprefix
          childRuntime hinclude) with
    ⟨hchildLookup, hchildImplementation, hchildMerge⟩
  exact
    hchildren responseName field fields prefixTail hgroup hprefix childDepth
      childRuntime childIdentity hlt hinclude hchildLookup
      hchildImplementation hchildMerge

inductive StoreSelectionSetRecursiveNormalizationTreeValidationState
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues)
    (variableDefinitions : List VariableDefinition) :
    Nat -> Name -> Name -> Name -> Option DataModel.ObjectRef ->
      List Selection -> Type where
  | mk {depth : Nat} {collectParent validParent runtimeType : Name}
      {identity : Option DataModel.ObjectRef} {selectionSet : List Selection}
      (parentRuntime :
        ScopedParentRuntimeApplies schema runtimeType validParent)
      (parentEq : collectParent = validParent)
      (parentObject : schema.objectType validParent)
      (lookup :
        NormalForm.selectionSetLookupValid schema validParent selectionSet)
      (implementation :
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions validParent selectionSet)
      (merge :
        FieldMerge.fieldsInSetCanMerge schema validParent selectionSet)
      (outputCompatible :
        ∀ responseName field fields prefixTail,
          (responseName, field :: fields) ∈
            GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet ->
          (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
          ∀ childRuntime,
            schema.typeIncludesObjectBool
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              childRuntime = true ->
            ∀ candidate, candidate ∈ field :: prefixTail ->
              ∀ scopedField,
                scopedField ∈ FieldMerge.collectFields schema validParent
                  selectionSet ->
                ScopedFieldMatchesExecutableIdentity scopedField candidate ->
                ScopedFieldRuntimeApplies schema runtimeType scopedField ->
                  schema.typeIncludesObjectBool scopedField.outputType.namedType
                    childRuntime = true)
      (normalizedSelectionSet : List Selection)
      (normalization :
        SelectionSetFreshPlanNormalizationTree schema (store.resolvers schema)
          variableValues depth collectParent (.object runtimeType identity)
          selectionSet normalizedSelectionSet)
      (children :
        ∀ responseName field fields prefixTail,
          (responseName, field :: fields) ∈
            GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet ->
          (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
          ∀ childDepth childRuntime
            (childIdentity : Option DataModel.ObjectRef),
            childDepth + 1 < depth ->
            schema.typeIncludesObjectBool
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              childRuntime = true ->
              StoreSelectionSetRecursiveNormalizationTreeValidationState
                schema store variableValues variableDefinitions childDepth
                childRuntime childRuntime childRuntime childIdentity
                (GraphQL.Execution.mergedFieldSelectionSet
                  (field :: prefixTail))) :
      StoreSelectionSetRecursiveNormalizationTreeValidationState schema store
        variableValues variableDefinitions depth collectParent validParent
        runtimeType identity selectionSet

namespace StoreSelectionSetRecursiveNormalizationTreeValidationState

def mkWithNormalizationChildren
    {schema : Schema} {store : DataModel.Store}
    {variableValues : VariableValues}
    {variableDefinitions : List VariableDefinition}
    {depth : Nat}
    {collectParent validParent runtimeType : Name}
    {identity : Option DataModel.ObjectRef}
    {selectionSet normalizedSelectionSet : List Selection}
    (hparentRuntime :
      ScopedParentRuntimeApplies schema runtimeType validParent)
    (hparentEq : collectParent = validParent)
    (hparentObject : schema.objectType validParent)
    (hlookup :
      NormalForm.selectionSetLookupValid schema validParent selectionSet)
    (himplementation :
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions validParent selectionSet)
    (hmerge : FieldMerge.fieldsInSetCanMerge schema validParent selectionSet)
    (houtputCompatible :
      ∀ responseName field fields prefixTail,
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet ->
        (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
        ∀ childRuntime,
          schema.typeIncludesObjectBool
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            childRuntime = true ->
          ∀ candidate, candidate ∈ field :: prefixTail ->
            ∀ scopedField,
              scopedField ∈ FieldMerge.collectFields schema validParent
                selectionSet ->
              ScopedFieldMatchesExecutableIdentity scopedField candidate ->
              ScopedFieldRuntimeApplies schema runtimeType scopedField ->
                schema.typeIncludesObjectBool scopedField.outputType.namedType
                  childRuntime = true)
    (hnormalization :
      SelectionSetFreshPlanNormalizationTree schema (store.resolvers schema)
        variableValues depth collectParent (.object runtimeType identity)
        selectionSet normalizedSelectionSet)
    (hchildren :
      ∀ responseName field fields prefixTail,
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet ->
        (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
        ∀ childDepth childRuntime
          (childIdentity : Option DataModel.ObjectRef),
          childDepth + 1 < depth ->
          schema.typeIncludesObjectBool
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            childRuntime = true ->
            StoreSelectionSetRecursiveNormalizationTreeValidationState
              schema store variableValues variableDefinitions childDepth
              childRuntime childRuntime childRuntime childIdentity
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))) :
    StoreSelectionSetRecursiveNormalizationTreeValidationState schema store
      variableValues variableDefinitions depth collectParent validParent
      runtimeType identity selectionSet :=
  .mk hparentRuntime hparentEq hparentObject hlookup himplementation hmerge
    houtputCompatible normalizedSelectionSet hnormalization hchildren

noncomputable def toGroupedState
    {schema : Schema} {store : DataModel.Store}
    {variableValues : VariableValues}
    {variableDefinitions : List VariableDefinition}
    (_hschema : SchemaWellFormedness.schemaWellFormed schema)
    {depth : Nat}
    {collectParent validParent runtimeType : Name}
    {identity : Option DataModel.ObjectRef}
    {selectionSet : List Selection}
    (state :
      StoreSelectionSetRecursiveNormalizationTreeValidationState schema store
        variableValues variableDefinitions depth collectParent validParent
        runtimeType identity selectionSet) :
    RecursiveGroupedSelectionSetState schema (store.resolvers schema)
      variableValues depth collectParent (.object runtimeType identity)
      selectionSet := by
  induction depth using Nat.strongRecOn generalizing collectParent validParent
    runtimeType identity selectionSet with
  | ind depth ih =>
      cases state with
      | mk parentRuntime _parentEq _parentObject lookup implementation merge
          outputCompatible normalizedSelectionSet normalization children =>
          have hflat :
              VisitSubfieldsFlatCollects schema (store.resolvers schema)
                variableValues (depth + 1) collectParent
                (.object runtimeType identity) selectionSet (.object []) :=
            (SelectionSetFreshPlanNormalizationTree.normalizes
              normalization).rawFreshFlat.empty
          exact
            recursiveGroupedSelectionSetState_store_object_of_implementationValid
              schema store variableValues depth collectParent validParent
              runtimeType identity selectionSet variableDefinitions hflat
              parentRuntime lookup implementation merge
              (by
                intro responseName field fields prefixTail hgroup hprefix
                  childDepth childRuntime childIdentity hlt hinclude
                have hltSucc : childDepth.succ < depth := by
                  simpa [Nat.succ_eq_add_one] using hlt
                exact
                  ih childDepth (Nat.lt_of_succ_lt hltSucc)
                    (children responseName field fields prefixTail hgroup
                      hprefix childDepth childRuntime childIdentity hlt
                      hinclude))

end StoreSelectionSetRecursiveNormalizationTreeValidationState

abbrev StoreRecursiveFlatValidationProvider
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues)
    (variableDefinitions : List VariableDefinition) : Prop :=
  ∀ (depth : Nat) (collectParent validParent runtimeType : Name)
    (identity : Option DataModel.ObjectRef) (selectionSet : List Selection),
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    collectParent = validParent ->
    schema.objectType validParent ->
    NormalForm.selectionSetLookupValid schema validParent selectionSet ->
    Validation.selectionSetImplementationValidInScope schema
      variableDefinitions validParent selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
      VisitSubfieldsFlatCollects schema (store.resolvers schema)
        variableValues (depth + 1) collectParent
        (.object runtimeType identity) selectionSet (.object [])

abbrev StoreRecursiveRawFreshFlatValidationProvider
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues)
    (variableDefinitions : List VariableDefinition) : Prop :=
  ∀ (depth : Nat) (collectParent validParent runtimeType : Name)
    (identity : Option DataModel.ObjectRef) (selectionSet : List Selection),
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    collectParent = validParent ->
    schema.objectType validParent ->
    NormalForm.selectionSetLookupValid schema validParent selectionSet ->
    Validation.selectionSetImplementationValidInScope schema
      variableDefinitions validParent selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues collectParent
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childRuntime,
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          childRuntime = true ->
        ∀ candidate, candidate ∈ field :: prefixTail ->
          ∀ scopedField,
            scopedField ∈ FieldMerge.collectFields schema validParent
              selectionSet ->
            ScopedFieldMatchesExecutableIdentity scopedField candidate ->
            ScopedFieldRuntimeApplies schema runtimeType scopedField ->
              schema.typeIncludesObjectBool scopedField.outputType.namedType
                childRuntime = true) ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema (store.resolvers schema)
        variableValues (depth + 1) collectParent
        (.object runtimeType identity) selectionSet

namespace StoreRecursiveRawFreshFlatValidationProvider

def toFlat
    {schema : Schema} {store : DataModel.Store}
    {variableValues : VariableValues}
    {variableDefinitions : List VariableDefinition}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (freshFlat :
      StoreRecursiveRawFreshFlatValidationProvider schema store variableValues
        variableDefinitions) :
    StoreRecursiveFlatValidationProvider schema store variableValues
      variableDefinitions := by
  intro depth collectParent validParent runtimeType identity selectionSet
    hparentRuntime hparentEq hparentObject hlookup himplementation hmerge
  have houtputCompatible :
      ∀ responseName field fields prefixTail,
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet ->
        (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
        ∀ childRuntime,
          schema.typeIncludesObjectBool
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            childRuntime = true ->
          ∀ candidate, candidate ∈ field :: prefixTail ->
            ∀ scopedField,
              scopedField ∈ FieldMerge.collectFields schema validParent
                selectionSet ->
              ScopedFieldMatchesExecutableIdentity scopedField candidate ->
              ScopedFieldRuntimeApplies schema runtimeType scopedField ->
                schema.typeIncludesObjectBool scopedField.outputType.namedType
                  childRuntime = true := by
    intro responseName field fields prefixTail hgroup hprefix childRuntime
      hinclude candidate hcandidate scopedField hscoped hmatch hruntime
    exact
      collectFields_group_prefix_outputCompatible_of_concreteParent
        schema variableValues collectParent validParent runtimeType identity
        selectionSet responseName field fields prefixTail
        hschema
        hparentEq hparentObject hparentRuntime hlookup hmerge hgroup hprefix
        childRuntime hinclude candidate hcandidate scopedField hscoped hmatch
        hruntime
  exact
    (freshFlat depth collectParent validParent runtimeType identity selectionSet
      hparentRuntime hparentEq hparentObject hlookup himplementation hmerge
      houtputCompatible).empty

end StoreRecursiveRawFreshFlatValidationProvider

theorem storeRecursiveRawFreshFlatValidationProvider
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues)
    (variableDefinitions : List VariableDefinition) :
    StoreRecursiveRawFreshFlatValidationProvider schema store variableValues
      variableDefinitions := by
  intro depth collectParent _validParent runtimeType identity selectionSet
    _parentRuntime _parentEq _parentObject _lookup _implementation _merge
    _outputCompatible
  exact
    VisitSubfieldsFlatCollectsFreshPrefixes_all schema (store.resolvers schema)
      variableValues (depth + 1) collectParent
      (.object runtimeType identity) selectionSet

namespace StoreRecursiveFlatValidationProvider

noncomputable def toSelectionSetState
    {schema : Schema} {store : DataModel.Store}
    {variableValues : VariableValues}
    {variableDefinitions : List VariableDefinition}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (flatProvider :
      StoreRecursiveFlatValidationProvider schema store variableValues
        variableDefinitions) :
    ∀ (depth : Nat) (collectParent validParent runtimeType : Name)
      (identity : Option DataModel.ObjectRef) (selectionSet : List Selection),
      ScopedParentRuntimeApplies schema runtimeType validParent ->
      collectParent = validParent ->
      schema.objectType validParent ->
      NormalForm.selectionSetLookupValid schema validParent selectionSet ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions validParent selectionSet ->
      FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues depth collectParent (.object runtimeType identity)
          selectionSet := by
  intro depth
  induction depth using Nat.strongRecOn with
  | ind depth ih =>
      intro collectParent validParent runtimeType identity selectionSet
        hparentRuntime hparentEq hparentObject hlookup himplementation hmerge
      have hflat :
          VisitSubfieldsFlatCollects schema (store.resolvers schema)
            variableValues (depth + 1) collectParent
            (.object runtimeType identity) selectionSet (.object []) :=
        flatProvider depth collectParent validParent runtimeType identity
          selectionSet hparentRuntime hparentEq hparentObject hlookup
          himplementation hmerge
      have houtputCompatible :
          ∀ responseName field fields prefixTail,
            (responseName, field :: fields) ∈
              GraphQL.Execution.collectFields schema variableValues
                collectParent (.object runtimeType identity) selectionSet ->
            (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
            ∀ childRuntime,
              schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType
                  field.fieldName).getD field.fieldName)
                childRuntime = true ->
              ∀ candidate, candidate ∈ field :: prefixTail ->
                ∀ scopedField,
                  scopedField ∈ FieldMerge.collectFields schema validParent
                    selectionSet ->
                  ScopedFieldMatchesExecutableIdentity scopedField candidate ->
                  ScopedFieldRuntimeApplies schema runtimeType scopedField ->
                    schema.typeIncludesObjectBool
                      scopedField.outputType.namedType childRuntime = true := by
        intro responseName field fields prefixTail hgroup hprefix childRuntime
          hinclude candidate hcandidate scopedField hscoped hmatch hruntime
        exact
          collectFields_group_prefix_outputCompatible_of_concreteParent
            schema variableValues collectParent validParent runtimeType
            identity selectionSet responseName field fields prefixTail hschema
            hparentEq hparentObject hparentRuntime hlookup hmerge hgroup
            hprefix childRuntime hinclude candidate hcandidate scopedField
            hscoped hmatch hruntime
      apply
        recursiveGroupedSelectionSetState_store_object_of_implementationValid
          schema store variableValues depth collectParent validParent
          runtimeType identity selectionSet variableDefinitions hflat
          hparentRuntime hlookup himplementation hmerge
      · intro responseName field fields prefixTail hgroup hprefix childDepth
          childRuntime childIdentity hlt hinclude
        have hchildLookup :
            NormalForm.selectionSetLookupValid schema childRuntime
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail)) :=
          collectFields_group_prefix_mergedFieldSelectionSet_lookupValid_of_selectionSetImplementationValid_object
            schema variableDefinitions variableValues collectParent
            validParent runtimeType identity selectionSet responseName
            childRuntime field fields prefixTail hschema hparentRuntime
            himplementation hgroup hprefix
            (houtputCompatible responseName field fields prefixTail
              hgroup hprefix childRuntime hinclude)
        have hchildImplementation :
            Validation.selectionSetImplementationValidInScope schema
              variableDefinitions childRuntime
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail)) :=
          collectFields_group_prefix_mergedFieldSelectionSet_implementationValid_of_selectionSetImplementationValid_object
            schema variableDefinitions variableValues collectParent
            validParent runtimeType identity selectionSet responseName
            childRuntime field fields prefixTail hparentRuntime
            himplementation hgroup hprefix
            (houtputCompatible responseName field fields prefixTail
              hgroup hprefix childRuntime hinclude)
        have hchildMerge :
            ∀ objectType,
              FieldMerge.fieldsInSetCanMerge schema objectType
                (GraphQL.Execution.mergedFieldSelectionSet
                  (field :: prefixTail)) :=
          collectFields_group_prefix_mergedFieldSelectionSet_canMerge_lookupValid_object
            schema variableValues collectParent validParent runtimeType
            identity selectionSet responseName field fields prefixTail
            hlookup hmerge hparentRuntime hgroup hprefix
        have hchildObject : schema.objectType childRuntime :=
          SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
            hschema
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            childRuntime
            (List.contains_iff_mem.mp hinclude)
        have hchildParentRuntime :
            ScopedParentRuntimeApplies schema childRuntime childRuntime :=
          NormalForm.object_typeIncludesObjectBool_self schema hchildObject
        exact
          ih childDepth (Nat.lt_of_succ_lt hlt) childRuntime childRuntime
            childRuntime childIdentity
            (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
            hchildParentRuntime rfl hchildObject hchildLookup
            hchildImplementation (hchildMerge childRuntime)

end StoreRecursiveFlatValidationProvider

structure StoreRecursiveNormalizationTreeValidationInvariants
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues)
    (variableDefinitions : List VariableDefinition) : Type where
  schemaWellFormed : SchemaWellFormedness.schemaWellFormed schema
  normalization :
    ∀ (depth : Nat) (collectParent validParent runtimeType : Name)
      (identity : Option DataModel.ObjectRef) (selectionSet : List Selection),
      ScopedParentRuntimeApplies schema runtimeType validParent ->
      collectParent = validParent ->
      schema.objectType validParent ->
      NormalForm.selectionSetLookupValid schema validParent selectionSet ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions validParent selectionSet ->
      FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
      (∀ responseName field fields prefixTail,
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet ->
        (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
        ∀ childRuntime,
          schema.typeIncludesObjectBool
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            childRuntime = true ->
          ∀ candidate, candidate ∈ field :: prefixTail ->
            ∀ scopedField,
              scopedField ∈ FieldMerge.collectFields schema validParent
                selectionSet ->
              ScopedFieldMatchesExecutableIdentity scopedField candidate ->
              ScopedFieldRuntimeApplies schema runtimeType scopedField ->
                schema.typeIncludesObjectBool scopedField.outputType.namedType
                  childRuntime = true) ->
        { normalizedSelectionSet : List Selection //
          SelectionSetFreshPlanNormalizationTree schema (store.resolvers schema)
            variableValues depth collectParent (.object runtimeType identity)
            selectionSet normalizedSelectionSet }

namespace StoreRecursiveNormalizationTreeValidationInvariants

def ofNormalization
    {schema : Schema} {store : DataModel.Store}
    {variableValues : VariableValues}
    {variableDefinitions : List VariableDefinition}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (normalization :
      ∀ (depth : Nat) (collectParent validParent runtimeType : Name)
        (identity : Option DataModel.ObjectRef) (selectionSet : List Selection),
        ScopedParentRuntimeApplies schema runtimeType validParent ->
        collectParent = validParent ->
        schema.objectType validParent ->
        NormalForm.selectionSetLookupValid schema validParent selectionSet ->
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions validParent selectionSet ->
        FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
        (∀ responseName field fields prefixTail,
          (responseName, field :: fields) ∈
            GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet ->
          (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
          ∀ childRuntime,
            schema.typeIncludesObjectBool
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              childRuntime = true ->
            ∀ candidate, candidate ∈ field :: prefixTail ->
              ∀ scopedField,
                scopedField ∈ FieldMerge.collectFields schema validParent
                  selectionSet ->
                ScopedFieldMatchesExecutableIdentity scopedField candidate ->
                ScopedFieldRuntimeApplies schema runtimeType scopedField ->
                  schema.typeIncludesObjectBool scopedField.outputType.namedType
                    childRuntime = true) ->
          { normalizedSelectionSet : List Selection //
            SelectionSetFreshPlanNormalizationTree schema
              (store.resolvers schema) variableValues depth collectParent
              (.object runtimeType identity) selectionSet
              normalizedSelectionSet }) :
    StoreRecursiveNormalizationTreeValidationInvariants schema store
      variableValues variableDefinitions :=
  { schemaWellFormed := hschema
    normalization := normalization }

def ofRawFreshFlat
    {schema : Schema} {store : DataModel.Store}
    {variableValues : VariableValues}
    {variableDefinitions : List VariableDefinition}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (freshFlat :
      StoreRecursiveRawFreshFlatValidationProvider schema store variableValues
        variableDefinitions) :
    StoreRecursiveNormalizationTreeValidationInvariants schema store
      variableValues variableDefinitions :=
  ofNormalization hschema
    (by
      intro depth collectParent validParent runtimeType identity selectionSet
        hparentRuntime hparentEq hparentObject hlookup himplementation hmerge
        houtputCompatible
      exact
        ⟨executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues
                collectParent (.object runtimeType identity) selectionSet)),
          SelectionSetFreshPlanNormalizationTree.of_rawFreshFlat_collectedCollectFields
            (freshFlat depth collectParent validParent runtimeType identity
              selectionSet hparentRuntime hparentEq hparentObject hlookup
              himplementation hmerge houtputCompatible)⟩)

def toRawFreshFlat
    {schema : Schema} {store : DataModel.Store}
    {variableValues : VariableValues}
    {variableDefinitions : List VariableDefinition}
    (invariants :
      StoreRecursiveNormalizationTreeValidationInvariants schema store
        variableValues variableDefinitions) :
    StoreRecursiveRawFreshFlatValidationProvider schema store variableValues
      variableDefinitions := by
  intro depth collectParent validParent runtimeType identity selectionSet
    hparentRuntime hparentEq hparentObject hlookup himplementation hmerge
    houtputCompatible
  exact
    ((invariants.normalization depth collectParent validParent runtimeType
      identity selectionSet hparentRuntime hparentEq hparentObject hlookup
      himplementation hmerge houtputCompatible).property.normalizes).rawFreshFlat

def toFlat
    {schema : Schema} {store : DataModel.Store}
    {variableValues : VariableValues}
    {variableDefinitions : List VariableDefinition}
    (invariants :
      StoreRecursiveNormalizationTreeValidationInvariants schema store
        variableValues variableDefinitions) :
    StoreRecursiveFlatValidationProvider schema store variableValues
      variableDefinitions := by
  intro depth collectParent validParent runtimeType identity selectionSet
    hparentRuntime hparentEq hparentObject hlookup himplementation hmerge
  have freshFlat :
      StoreRecursiveRawFreshFlatValidationProvider schema store variableValues
        variableDefinitions :=
    invariants.toRawFreshFlat
  exact
    StoreRecursiveRawFreshFlatValidationProvider.toFlat
      invariants.schemaWellFormed freshFlat depth collectParent validParent
      runtimeType identity selectionSet hparentRuntime hparentEq
      hparentObject hlookup himplementation hmerge

end StoreRecursiveNormalizationTreeValidationInvariants

namespace StoreSelectionSetRecursiveNormalizationTreeValidationState

noncomputable def ofInvariants
    {schema : Schema} {store : DataModel.Store}
    {variableValues : VariableValues}
    {variableDefinitions : List VariableDefinition}
    (invariants :
      StoreRecursiveNormalizationTreeValidationInvariants schema store
        variableValues variableDefinitions)
    (depth : Nat) (collectParent validParent runtimeType : Name)
    (identity : Option DataModel.ObjectRef) (selectionSet : List Selection)
    (hparentRuntime :
      ScopedParentRuntimeApplies schema runtimeType validParent)
    (hparentEq : collectParent = validParent)
    (hparentObject : schema.objectType validParent)
    (hlookup :
      NormalForm.selectionSetLookupValid schema validParent selectionSet)
    (himplementation :
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions validParent selectionSet)
    (hmerge : FieldMerge.fieldsInSetCanMerge schema validParent
      selectionSet) :
    StoreSelectionSetRecursiveNormalizationTreeValidationState schema store
      variableValues variableDefinitions depth collectParent validParent
      runtimeType identity selectionSet := by
  induction depth using Nat.strongRecOn generalizing collectParent validParent
    runtimeType identity selectionSet with
  | ind depth ih =>
      have houtputCompatible :
          ∀ responseName field fields prefixTail,
            (responseName, field :: fields) ∈
              GraphQL.Execution.collectFields schema variableValues
                collectParent (.object runtimeType identity) selectionSet ->
            (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
            ∀ childRuntime,
              schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType
                  field.fieldName).getD field.fieldName)
                childRuntime = true ->
              ∀ candidate, candidate ∈ field :: prefixTail ->
                ∀ scopedField,
                  scopedField ∈ FieldMerge.collectFields schema validParent
                    selectionSet ->
                  ScopedFieldMatchesExecutableIdentity scopedField candidate ->
                  ScopedFieldRuntimeApplies schema runtimeType scopedField ->
                    schema.typeIncludesObjectBool
                      scopedField.outputType.namedType childRuntime = true := by
        intro responseName field fields prefixTail hgroup hprefix childRuntime
          hinclude candidate hcandidate scopedField hscoped hmatch hruntime
        exact
          collectFields_group_prefix_outputCompatible_of_concreteParent
            schema variableValues collectParent validParent runtimeType
            identity selectionSet responseName field fields prefixTail
            invariants.schemaWellFormed hparentEq hparentObject
            hparentRuntime hlookup hmerge hgroup hprefix childRuntime hinclude
            candidate hcandidate scopedField hscoped hmatch hruntime
      let normalizationWitness :=
        invariants.normalization depth collectParent validParent runtimeType
          identity selectionSet hparentRuntime hparentEq hparentObject hlookup
          himplementation hmerge houtputCompatible
      exact
        mkWithNormalizationChildren hparentRuntime hparentEq hparentObject
          hlookup himplementation hmerge houtputCompatible
          normalizationWitness.property
          (by
            intro responseName field fields prefixTail hgroup hprefix
              childDepth childRuntime childIdentity hlt hincludes
            have hchildLookup :
                NormalForm.selectionSetLookupValid schema childRuntime
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail)) :=
              collectFields_group_prefix_mergedFieldSelectionSet_lookupValid_of_selectionSetImplementationValid_object
                schema variableDefinitions variableValues collectParent
                validParent runtimeType identity selectionSet responseName
                childRuntime field fields prefixTail invariants.schemaWellFormed
                hparentRuntime himplementation hgroup hprefix
                (houtputCompatible responseName field fields prefixTail
                  hgroup hprefix childRuntime hincludes)
            have hchildImplementation :
                Validation.selectionSetImplementationValidInScope schema
                  variableDefinitions childRuntime
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail)) :=
              collectFields_group_prefix_mergedFieldSelectionSet_implementationValid_of_selectionSetImplementationValid_object
                schema variableDefinitions variableValues collectParent
                validParent runtimeType identity selectionSet responseName
                childRuntime field fields prefixTail hparentRuntime
                himplementation hgroup hprefix
                (houtputCompatible responseName field fields prefixTail
                  hgroup hprefix childRuntime hincludes)
            have hchildMerge :
                ∀ objectType,
                  FieldMerge.fieldsInSetCanMerge schema objectType
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail)) :=
              collectFields_group_prefix_mergedFieldSelectionSet_canMerge_lookupValid_object
                schema variableValues collectParent validParent runtimeType
                identity selectionSet responseName field fields prefixTail
                hlookup hmerge hparentRuntime hgroup hprefix
            have hchildParentRuntime :
                ScopedParentRuntimeApplies schema childRuntime childRuntime := by
              have hchildObject : schema.objectType childRuntime :=
                SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                  invariants.schemaWellFormed
                  ((schema.fieldReturnType? field.parentType
                    field.fieldName).getD field.fieldName)
                  childRuntime
                  (List.contains_iff_mem.mp hincludes)
              exact NormalForm.object_typeIncludesObjectBool_self schema
                hchildObject
            have hchildObject : schema.objectType childRuntime :=
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                invariants.schemaWellFormed
                ((schema.fieldReturnType? field.parentType
                  field.fieldName).getD field.fieldName)
                childRuntime
                (List.contains_iff_mem.mp hincludes)
            have hltSucc : childDepth.succ < depth := by
              simpa [Nat.succ_eq_add_one] using hlt
            exact
              ih childDepth (Nat.lt_of_succ_lt hltSucc) childRuntime
                childRuntime childRuntime childIdentity
                (GraphQL.Execution.mergedFieldSelectionSet
                  (field :: prefixTail))
                hchildParentRuntime rfl hchildObject hchildLookup
                hchildImplementation (hchildMerge childRuntime))

end StoreSelectionSetRecursiveNormalizationTreeValidationState

def recursiveGroupedSelectionSetState_store_object_of_fieldNormal_childLocalFacts
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name)
    (identity : Option DataModel.ObjectRef)
    (selectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    SchemaWellFormedness.schemaWellFormed schema ->
    VisitSubfieldsFlatCollects schema (store.resolvers schema) variableValues
      (depth + 1) parentType (.object runtimeType identity) selectionSet
      (.object []) ->
    ScopedParentRuntimeApplies schema runtimeType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      selectionSet ->
    NormalForm.selectionSetLookupValid schema parentType selectionSet ->
    Validation.selectionSetImplementationValidInScope schema variableDefinitions
      parentType selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    NormalForm.responseNamesNodup selectionSet ->
    (∀ responseName field fields,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues parentType
          (.object runtimeType identity) selectionSet ->
      ∀ childDepth childRuntime (childIdentity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          childRuntime = true ->
        NormalForm.selectionSetLookupValid schema childRuntime
          field.selectionSet ->
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions childRuntime field.selectionSet ->
        (∀ objectType,
          FieldMerge.fieldsInSetCanMerge schema objectType
            field.selectionSet) ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth childRuntime
          (.object childRuntime childIdentity) field.selectionSet) ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth parentType (.object runtimeType identity)
        selectionSet := by
  intro hschema flat hparentRuntime hvalid hlookupValid himplementation
    hmerge hall hfree hnodup hchildren
  apply
    recursiveGroupedSelectionSetState_store_object_of_implementationValid_childLocalFacts
      schema store variableValues depth parentType parentType runtimeType
      identity selectionSet variableDefinitions hschema flat hparentRuntime
      hvalid hlookupValid himplementation hmerge
  · intro responseName field fields prefixTail hgroup hprefix childRuntime
      hinclude candidate hcandidate scopedField hscopedMem hmatch _hruntime
    rcases
        FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_prefix_empty
          schema variableValues parentType (.object runtimeType identity)
          selectionSet hall hfree hnodup hgroup hprefix with
      ⟨_hfields, hprefixTail⟩
    subst prefixTail
    have hcandidateEq : candidate = field := by
      simpa using hcandidate
    subst candidate
    have hparents :
        CollectedGroupsParent parentType
          (GraphQL.Execution.collectFields schema variableValues parentType
            (.object runtimeType identity) selectionSet) :=
      collectFields_parent schema variableValues parentType
        (.object runtimeType identity) selectionSet
    have hfieldParent : field.parentType = parentType :=
      hparents responseName (field :: fields) hgroup field (by simp)
    have hscopedParent : scopedField.parentType = parentType :=
      FreshPrefixSelectionDerivation.fieldMerge_collectFields_parent_of_allFields
        schema parentType selectionSet scopedField hall hscopedMem
    have hparent : field.parentType = scopedField.parentType :=
      hfieldParent.trans hscopedParent.symm
    have houtput :
        scopedField.outputType.namedType =
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName) :=
      FreshPrefixSelectionDerivation.scopedField_outputType_eq_fieldReturnType_of_identity_match
        schema variableDefinitions parentType selectionSet scopedField field
        hvalid hscopedMem hparent hmatch
    simpa [houtput] using hinclude
  · intro responseName field fields prefixTail hgroup hprefix childDepth
      childRuntime childIdentity hlt hinclude hchildLookup
      hchildImplementation hchildMerge
    rcases
        FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_prefix_empty
          schema variableValues parentType (.object runtimeType identity)
          selectionSet hall hfree hnodup hgroup hprefix with
      ⟨_hfields, hprefixTail⟩
    subst prefixTail
    have hchildLookup' :
        NormalForm.selectionSetLookupValid schema childRuntime
          field.selectionSet := by
      simpa using hchildLookup
    have hchildImplementation' :
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions childRuntime field.selectionSet := by
      simpa using hchildImplementation
    have hchildMerge' :
        ∀ objectType,
          FieldMerge.fieldsInSetCanMerge schema objectType
            field.selectionSet := by
      intro objectType
      simpa using hchildMerge objectType
    simpa using
      hchildren responseName field fields hgroup childDepth childRuntime
        childIdentity hlt hinclude hchildLookup' hchildImplementation'
        hchildMerge'

def recursiveGroupedSelectionSetState_store_object_of_fieldNormal_generatedChildren
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name)
    (identity : Option DataModel.ObjectRef)
    (selectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    SchemaWellFormedness.schemaWellFormed schema ->
    VisitSubfieldsFlatCollects schema (store.resolvers schema) variableValues
      (depth + 1) parentType (.object runtimeType identity) selectionSet
      (.object []) ->
    ScopedParentRuntimeApplies schema runtimeType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      selectionSet ->
    NormalForm.selectionSetLookupValid schema parentType selectionSet ->
    Validation.selectionSetImplementationValidInScope schema variableDefinitions
      parentType selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    NormalForm.responseNamesNodup selectionSet ->
    (∀ responseName fieldName arguments directives childSelectionSet,
      Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ selectionSet ->
      generatedNormalizedFieldChild schema
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        childSelectionSet) ->
    (∀ responseName field fields,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues parentType
          (.object runtimeType identity) selectionSet ->
      ∀ childDepth childRuntime (childIdentity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          childRuntime = true ->
        generatedNormalizedFieldChild schema
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          field.selectionSet ->
        NormalForm.selectionSetLookupValid schema childRuntime
          field.selectionSet ->
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions childRuntime field.selectionSet ->
        (∀ objectType,
          FieldMerge.fieldsInSetCanMerge schema objectType
            field.selectionSet) ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth childRuntime
          (.object childRuntime childIdentity) field.selectionSet) ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth parentType (.object runtimeType identity)
        selectionSet := by
  intro hschema flat hparentRuntime hvalid hlookupValid himplementation
    hmerge hall hfree hnodup hgeneratedChildren hchildren
  apply
    recursiveGroupedSelectionSetState_store_object_of_fieldNormal_childLocalFacts
      schema store variableValues depth parentType runtimeType identity
      selectionSet variableDefinitions hschema flat hparentRuntime hvalid
      hlookupValid himplementation hmerge hall hfree hnodup
  intro responseName field fields hgroup childDepth childRuntime childIdentity
    hlt hinclude hchildLookup hchildImplementation hchildMerge
  have hgenerated :
      generatedNormalizedFieldChild schema
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        field.selectionSet :=
    generatedNormalizedFieldChild_of_collectFields_field_layer
      schema variableValues parentType (.object runtimeType identity)
      selectionSet hall hfree hnodup hgeneratedChildren
      (field := field) (fields := fields) (prefixTail := []) hgroup
      (by
        intro candidate hcandidate
        cases hcandidate)
  exact
    hchildren responseName field fields hgroup childDepth childRuntime
      childIdentity hlt hinclude hgenerated hchildLookup hchildImplementation
      hchildMerge

def recursiveGroupedSelectionSetState_store_object_selectionSet_canMerge
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : Option DataModel.ObjectRef)
    (selectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    FreshPrefixSelectionDerivation schema variableValues parentType
      (.object runtimeType identity) selectionSet ->
    ScopedParentRuntimeApplies schema runtimeType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues parentType
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth childRuntime (childIdentity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          childRuntime = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth childRuntime
          (.object childRuntime childIdentity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth parentType (.object runtimeType identity)
        selectionSet := by
  intro derivation hparentRuntime hvalid hmerge hchildren
  exact
    RecursiveGroupedSelectionSetState.of_localFreshPrefixInvariants
      (selectionSetLocalFreshPrefixInvariants_store_object_selectionSet_canMerge
        schema store variableValues depth parentType runtimeType identity
        selectionSet variableDefinitions derivation hparentRuntime hvalid hmerge)
      hchildren

theorem executeOperationAtDepth_completeNormalizeOperation_of_recursiveGroupedOperationState
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    RecursiveGroupedOperationState schema (store.resolvers schema)
      variableValues operation depth store.rootExecutionValue ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hschema hvalid hcomplete state
  unfold executeOperationAtDepth
  exact
    completeNormalizationPreservesUngroupedExecution_of_recursiveGroupedOperationState
      schema operation (store.resolvers schema) variableValues depth
      store.rootExecutionValue state hschema hvalid hcomplete

theorem executeOperationAtDepth_completeNormalizeOperation_of_filter_recursiveGroupedStates
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    store.wellTyped schema ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    (∀ runtimeCase,
      runtimeCase ∈
        NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
      NormalForm.CompleteNormalization.variableValuesAgreeWithCase
        variableValues runtimeCase
        (NormalForm.operationBoolVars operation) ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth operation.rootType store.rootExecutionValue
        (NormalForm.filterSelectionSetBoolCase runtimeCase
          operation.selectionSet)) ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation)
        (depth + 1) := by
  intro hschema hvalid hstore hcomplete hstates
  unfold executeOperationAtDepth
  have hrootObject : schema.objectType operation.rootType :=
    NormalForm.CompleteNormalization.operation_root_object_of_valid hschema
      hvalid
  have hobject :
      NormalForm.objectTypeNameBool schema operation.rootType = true :=
    NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType
      schema hrootObject
  have hsource :
      ∃ runtimeType ref,
        store.rootExecutionValue = .object runtimeType ref
          ∧ schema.typeIncludesObjectBool operation.rootType runtimeType =
            true := by
    have hinclude :
        schema.typeIncludesObject operation.rootType store.root.typeName := by
      have hrootType : operation.rootType = schema.queryType :=
        Validation.operationDefinitionValid_rootType_eq hvalid
      simpa [hrootType] using hstore.1
    refine
      ⟨store.root.typeName, some (DataModel.objectRefOfId store.root.id),
        ?_, ?_⟩
    · simp [DataModel.Store.rootExecutionValue]
    · exact typeIncludesObjectBool_eq_true_of_typeIncludesObject schema hinclude
  apply executeQueryAtDepth_completeNormalizeOperation_eq_of_filter_recursiveGroupedStates
    schema operation (store.resolvers schema) variableValues depth
    store.rootExecutionValue hschema hcomplete hobject hsource
  · intro runtimeCase _hruntime _hagrees
    exact
      NormalForm.CompleteNormalization.filterSelectionSetBoolCase_directiveFree
        schema runtimeCase operation.selectionSet
  · intro runtimeCase _hruntime _hagrees
    exact
      NormalForm.CompleteNormalization.filterSelectionSetBoolCase_selectionSetSemanticsReady
        schema runtimeCase operation.rootType operation.selectionSet
        (NormalForm.CompleteNormalization.operation_selectionSetSemanticsReady_of_valid
          hschema hvalid)
  · intro runtimeCase _hruntime _hagrees
    exact
      NormalForm.CompleteNormalization.fieldsInSetCanMerge_filterSelectionSetBoolCase
        schema runtimeCase
        (Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid)
  · exact hstates

theorem executeOperationAtDepth_completeNormalizeOperation_of_filter_flatValidationProvider
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    store.wellTyped schema ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    NormalForm.CompleteNormalization.completeBoolCasesCompositeChildrenSurvive
      operation ->
    StoreRecursiveFlatValidationProvider schema store variableValues
      operation.variableDefinitions ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation)
        (depth + 1) := by
  intro hschema hvalid hstore hcomplete hsurvive flatProvider
  apply executeOperationAtDepth_completeNormalizeOperation_of_filter_recursiveGroupedStates
    schema store variableValues operation depth hschema hvalid hstore
    hcomplete
  intro runtimeCase hruntime _hagrees
  have hrootApplies :
      rootSourceAppliesBool schema operation store.rootExecutionValue = true :=
    rootSourceAppliesBool_store_rootExecutionValue schema store operation
      hstore hvalid
  have hparentRuntime :
      ScopedParentRuntimeApplies schema store.root.typeName operation.rootType :=
    ScopedParentRuntimeApplies.of_rootSourceAppliesBool schema operation
      store.root.typeName (DataModel.objectRefOfId store.root.id)
      (by simpa [DataModel.Store.rootExecutionValue] using hrootApplies)
  have hrootObject : schema.objectType operation.rootType :=
    NormalForm.CompleteNormalization.operation_root_object_of_valid hschema
      hvalid
  have hrootLookup :
      NormalForm.selectionSetLookupValid schema operation.rootType
        operation.selectionSet :=
    NormalForm.selectionSetLookupValid_of_selectionSetValid
      operation.selectionSet
      (Validation.operationDefinitionValid_selectionSetValid hvalid)
  have hfilteredLookup :
      NormalForm.selectionSetLookupValid schema operation.rootType
        (NormalForm.filterSelectionSetBoolCase runtimeCase
          operation.selectionSet) :=
    NormalForm.CompleteNormalization.filterSelectionSetBoolCase_selectionSetLookupValid
      schema runtimeCase operation.rootType operation.selectionSet hrootLookup
  have hfilteredImplementation :
      Validation.selectionSetImplementationValidInScope schema
        operation.variableDefinitions operation.rootType
        (NormalForm.filterSelectionSetBoolCase runtimeCase
          operation.selectionSet) :=
    NormalForm.CompleteNormalization.completeFilteredBoolCasesImplementationValid_of_compositeChildrenSurvive
      schema operation hvalid hsurvive runtimeCase hruntime
  have hfilteredMerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        (NormalForm.filterSelectionSetBoolCase runtimeCase
          operation.selectionSet) :=
    NormalForm.CompleteNormalization.fieldsInSetCanMerge_filterSelectionSetBoolCase
      schema runtimeCase
      (Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid)
  simpa [DataModel.Store.rootExecutionValue] using
    StoreRecursiveFlatValidationProvider.toSelectionSetState
      (schema := schema) (store := store) (variableValues := variableValues)
      (variableDefinitions := operation.variableDefinitions) hschema
      flatProvider depth operation.rootType operation.rootType
      store.root.typeName (some (DataModel.objectRefOfId store.root.id))
      (NormalForm.filterSelectionSetBoolCase runtimeCase
        operation.selectionSet)
      hparentRuntime rfl hrootObject hfilteredLookup
      hfilteredImplementation hfilteredMerge

theorem executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_recursiveGroupedOperationState
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    RecursiveGroupedOperationState schema (store.resolvers schema)
      variableValues operation depth store.rootExecutionValue ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hschema hvalid hcomplete state
  unfold executeOperationAtDepth GraphQL.DataModel.executeOperationAtDepth
  exact
    executeQueryAtDepth_semanticsPreserved_via_completeNormalization_of_recursiveGroupedOperationState
      schema operation (store.resolvers schema) variableValues depth
      store.rootExecutionValue state hschema hvalid hcomplete

def recursiveGroupedStoreOperationStateAtDepth
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation) :
    Nat -> Type
  | 0 => PUnit
  | depth + 1 =>
      RecursiveGroupedOperationState schema (store.resolvers schema)
        variableValues operation depth store.rootExecutionValue

namespace StoreRecursiveFlatValidationProvider

noncomputable def toOperationStateAtDepth
    {schema : Schema} {store : DataModel.Store}
    {variableValues : VariableValues} {operation : Operation}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hstore : store.wellTyped schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (flatProvider :
      StoreRecursiveFlatValidationProvider schema store variableValues
        operation.variableDefinitions) :
    ∀ depth,
      recursiveGroupedStoreOperationStateAtDepth schema store variableValues
        operation depth
  | 0 => PUnit.unit
  | depth + 1 =>
      have hrootObject : schema.objectType operation.rootType := by
        have hrootType : operation.rootType = schema.queryType :=
          Validation.operationDefinitionValid_rootType_eq hvalid
        rw [hrootType]
        exact hschema.2.1
      { root :=
          rootSourceAppliesBool_store_rootExecutionValue schema store operation
            hstore hvalid
        selectionSet := by
          simpa [DataModel.Store.rootExecutionValue] using
            toSelectionSetState (schema := schema) (store := store)
              (variableValues := variableValues)
              (variableDefinitions := operation.variableDefinitions)
              hschema flatProvider depth operation.rootType
              operation.rootType store.root.typeName
              (some (DataModel.objectRefOfId store.root.id))
              operation.selectionSet
              (ScopedParentRuntimeApplies.of_rootSourceAppliesBool schema
                operation store.root.typeName
                (DataModel.objectRefOfId store.root.id)
                (rootSourceAppliesBool_store_rootExecutionValue schema store
                  operation hstore hvalid))
              rfl hrootObject
              (NormalForm.selectionSetLookupValid_of_selectionSetValid
                operation.selectionSet
                (Validation.operationDefinitionValid_selectionSetValid hvalid))
              ((Validation.operationDefinitionValid_selectionSetImplementationValid
                hvalid).1)
              (Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid) }

end StoreRecursiveFlatValidationProvider

structure StoreOperationAtDepthNormalizationTreeValidationState
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) : Type where
  wellTyped : store.wellTyped schema
  valid : Validation.operationDefinitionValid schema operation
  rootState :
    StoreSelectionSetRecursiveNormalizationTreeValidationState schema store
      variableValues operation.variableDefinitions depth operation.rootType
      operation.rootType store.root.typeName
      (some (DataModel.objectRefOfId store.root.id))
      operation.selectionSet

namespace StoreOperationAtDepthNormalizationTreeValidationState

def of_validRootOperation
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat)
    (hstore : store.wellTyped schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (houtputCompatible :
      ∀ responseName field fields prefixTail,
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues
            operation.rootType store.rootExecutionValue
            operation.selectionSet ->
        (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
        ∀ childRuntime,
          schema.typeIncludesObjectBool
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            childRuntime = true ->
          ∀ candidate, candidate ∈ field :: prefixTail ->
            ∀ scopedField,
              scopedField ∈ FieldMerge.collectFields schema operation.rootType
                operation.selectionSet ->
              ScopedFieldMatchesExecutableIdentity scopedField candidate ->
              ScopedFieldRuntimeApplies schema store.root.typeName
                scopedField ->
                schema.typeIncludesObjectBool scopedField.outputType.namedType
                  childRuntime = true)
    (normalizedSelectionSet : List Selection)
    (hnormalization :
      SelectionSetFreshPlanNormalizationTree schema (store.resolvers schema)
        variableValues depth operation.rootType store.rootExecutionValue
        operation.selectionSet normalizedSelectionSet)
    (hchildren :
      ∀ responseName field fields prefixTail,
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues
            operation.rootType store.rootExecutionValue operation.selectionSet ->
        (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
        ∀ childDepth childRuntime
          (childIdentity : Option DataModel.ObjectRef),
          childDepth + 1 < depth ->
          schema.typeIncludesObjectBool
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            childRuntime = true ->
            StoreSelectionSetRecursiveNormalizationTreeValidationState
              schema store variableValues operation.variableDefinitions
              childDepth childRuntime childRuntime childRuntime childIdentity
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))) :
    StoreOperationAtDepthNormalizationTreeValidationState schema store
      variableValues operation depth :=
  have hrootObject : schema.objectType operation.rootType := by
    have hrootType : operation.rootType = schema.queryType :=
      Validation.operationDefinitionValid_rootType_eq hvalid
    rw [hrootType]
    exact hschema.2.1
  { wellTyped := hstore
    valid := hvalid
    rootState :=
      StoreSelectionSetRecursiveNormalizationTreeValidationState.mkWithNormalizationChildren
        (ScopedParentRuntimeApplies.of_rootSourceAppliesBool schema operation
          store.root.typeName (DataModel.objectRefOfId store.root.id)
          (rootSourceAppliesBool_store_rootExecutionValue schema store
            operation hstore hvalid))
        rfl
        hrootObject
        (NormalForm.selectionSetLookupValid_of_selectionSetValid
          operation.selectionSet
          (Validation.operationDefinitionValid_selectionSetValid hvalid))
        ((Validation.operationDefinitionValid_selectionSetImplementationValid
          hvalid).1)
        (Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid)
        (by
          intro responseName field fields prefixTail hgroup hprefix
            childRuntime hinclude candidate hcandidate scopedField hscoped
            hmatch hruntime
          exact
            houtputCompatible responseName field fields prefixTail
              (by simpa [DataModel.Store.rootExecutionValue] using hgroup)
              hprefix childRuntime hinclude candidate hcandidate scopedField
              hscoped hmatch hruntime)
        (by simpa [DataModel.Store.rootExecutionValue] using
          hnormalization)
        (by
          intro responseName field fields prefixTail hgroup hprefix childDepth
            childRuntime childIdentity hlt hincludes
          exact
            hchildren responseName field fields prefixTail
              (by simpa [DataModel.Store.rootExecutionValue] using hgroup)
              hprefix childDepth childRuntime childIdentity hlt hincludes) }

noncomputable def ofInvariants
    {schema : Schema} {store : DataModel.Store}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat}
    (invariants :
      StoreRecursiveNormalizationTreeValidationInvariants schema store
        variableValues operation.variableDefinitions)
    (hstore : store.wellTyped schema)
    (hvalid : Validation.operationDefinitionValid schema operation) :
    StoreOperationAtDepthNormalizationTreeValidationState schema store
      variableValues operation depth :=
  have hrootObject : schema.objectType operation.rootType := by
    have hrootType : operation.rootType = schema.queryType :=
      Validation.operationDefinitionValid_rootType_eq hvalid
    rw [hrootType]
    exact invariants.schemaWellFormed.2.1
  { wellTyped := hstore
    valid := hvalid
    rootState :=
      StoreSelectionSetRecursiveNormalizationTreeValidationState.ofInvariants
        invariants depth operation.rootType operation.rootType
        store.root.typeName (some (DataModel.objectRefOfId store.root.id))
        operation.selectionSet
        (ScopedParentRuntimeApplies.of_rootSourceAppliesBool schema operation
          store.root.typeName (DataModel.objectRefOfId store.root.id)
          (rootSourceAppliesBool_store_rootExecutionValue schema store
            operation hstore hvalid))
        rfl
        hrootObject
        (NormalForm.selectionSetLookupValid_of_selectionSetValid
          operation.selectionSet
          (Validation.operationDefinitionValid_selectionSetValid hvalid))
        ((Validation.operationDefinitionValid_selectionSetImplementationValid
          hvalid).1)
        (Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid) }

noncomputable def toRecursiveGroupedStoreOperationStateAtDepth
    {schema : Schema} {store : DataModel.Store}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (state :
      StoreOperationAtDepthNormalizationTreeValidationState schema store
        variableValues operation depth) :
    recursiveGroupedStoreOperationStateAtDepth schema store variableValues
      operation (depth + 1) :=
  { root :=
      rootSourceAppliesBool_store_rootExecutionValue schema store operation
        state.wellTyped state.valid
    selectionSet := by
      simpa [DataModel.Store.rootExecutionValue] using
        state.rootState.toGroupedState hschema }

end StoreOperationAtDepthNormalizationTreeValidationState

theorem executeOperationAtDepth_completeNormalizeOperation_of_normalizationTreeValidationState
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    StoreOperationAtDepthNormalizationTreeValidationState schema store
      variableValues operation depth ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hschema hcomplete state
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_recursiveGroupedOperationState
      schema store variableValues operation depth hschema state.valid
      hcomplete
      (state.toRecursiveGroupedStoreOperationStateAtDepth hschema)

theorem executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_normalizationTreeValidationState
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    StoreOperationAtDepthNormalizationTreeValidationState schema store
      variableValues operation depth ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hschema hcomplete state
  exact
    executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_recursiveGroupedOperationState
      schema store variableValues operation depth hschema state.valid
      hcomplete
      (state.toRecursiveGroupedStoreOperationStateAtDepth hschema)

theorem executeOperationAtDepth_completeNormalizeOperation_iff_semanticsPreserved
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      ((executeOperationAtDepth schema store variableValues operation depth
        =
       executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth)
      ↔
      (executeOperationAtDepth schema store variableValues operation depth
        =
       GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation depth)) := by
  intro hschema hvalid hcomplete
  unfold executeOperationAtDepth GraphQL.DataModel.executeOperationAtDepth
  exact
    completeNormalizationPreservesUngroupedExecution_iff_source_eq_spec
      schema operation (store.resolvers schema) variableValues depth
      store.rootExecutionValue hschema hvalid hcomplete

theorem specExecuteOperationAtDepth_completeNormalizeOperation_eq_ungrouped
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
          (NormalForm.completeNormalizeOperation schema operation) depth
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth := by
  intro hschema hcomplete
  unfold executeOperationAtDepth GraphQL.DataModel.executeOperationAtDepth
  exact
    specExecution_eq_ungroupedExecution_of_completeNormalizeOperation
      schema operation (store.resolvers schema) variableValues depth
      store.rootExecutionValue hschema hcomplete

theorem completeNormalized_specExecution_eq_ungroupedExecution
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
          (NormalForm.completeNormalizeOperation schema operation) depth
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth := by
  exact
    specExecuteOperationAtDepth_completeNormalizeOperation_eq_ungrouped
      schema store variableValues operation depth

theorem specExecuteOperationAtDepth_eq_ungrouped_of_generatedNormalOperation
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.selectionsAllFields operation.selectionSet ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.operationNormal schema operation ->
    (∀ responseName fieldName arguments directives childSelectionSet,
      Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ operation.selectionSet ->
      generatedNormalizedFieldChild schema
        ((schema.fieldReturnType? operation.rootType fieldName).getD
          fieldName)
        childSelectionSet) ->
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
          operation depth
        =
      executeOperationAtDepth schema store variableValues operation depth := by
  intro hschema hall hfree hnormal hchildren
  unfold executeOperationAtDepth GraphQL.DataModel.executeOperationAtDepth
  exact
    (executeQueryAtDepth_eq_spec_of_generatedNormalOperation schema operation
      (store.resolvers schema) variableValues depth store.rootExecutionValue
      hschema hall hfree hnormal hchildren).symm

theorem generatedNormalOperation_specExecution_eq_ungroupedExecution
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.selectionsAllFields operation.selectionSet ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.operationNormal schema operation ->
    (∀ responseName fieldName arguments directives childSelectionSet,
      Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ operation.selectionSet ->
      generatedNormalizedFieldChild schema
        ((schema.fieldReturnType? operation.rootType fieldName).getD
          fieldName)
        childSelectionSet) ->
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
          operation depth
        =
      executeOperationAtDepth schema store variableValues operation depth := by
  exact
    specExecuteOperationAtDepth_eq_ungrouped_of_generatedNormalOperation
      schema store variableValues operation depth

theorem executeOperationAtDepth_completeNormalizeOperation_eq_spec
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      executeOperationAtDepth schema store variableValues
          (NormalForm.completeNormalizeOperation schema operation) depth
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth := by
  intro hschema hcomplete
  exact
    (specExecuteOperationAtDepth_completeNormalizeOperation_eq_ungrouped
      schema store variableValues operation depth hschema hcomplete).symm

theorem executeOperationAtDepth_completeNormalizeOperation_depth_zero
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation) :
      executeOperationAtDepth schema store variableValues operation 0
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) 0 := by
  unfold executeOperationAtDepth
  exact
    executeQueryAtDepth_completeNormalizeOperation_depth_zero
      schema operation (store.resolvers schema) variableValues
      store.rootExecutionValue

theorem executeOperationAtDepth_semanticsPreserved_of_completeNormalizeOperation
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    executeOperationAtDepth schema store variableValues operation depth
      =
    executeOperationAtDepth schema store variableValues
      (NormalForm.completeNormalizeOperation schema operation) depth ->
      executeOperationAtDepth schema store variableValues operation depth
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation depth := by
  intro hschema hvalid hcomplete hpreserved
  exact
    (executeOperationAtDepth_completeNormalizeOperation_iff_semanticsPreserved
      schema store variableValues operation depth hschema hvalid hcomplete).mp
      hpreserved

theorem executeOperationAtDepth_completeNormalizeOperation_of_semanticsPreserved
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    executeOperationAtDepth schema store variableValues operation depth
      =
    GraphQL.DataModel.executeOperationAtDepth schema store variableValues
      operation depth ->
      executeOperationAtDepth schema store variableValues operation depth
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth := by
  intro hschema hvalid hcomplete hsemantics
  exact
    (executeOperationAtDepth_completeNormalizeOperation_iff_semanticsPreserved
      schema store variableValues operation depth hschema hvalid hcomplete).mpr
      hsemantics

theorem executeOperationAtDepth_completeNormalizeOperation_of_recursiveGroupedStoreOperationStateAtDepth
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      recursiveGroupedStoreOperationStateAtDepth schema store variableValues
        operation depth ->
      executeOperationAtDepth schema store variableValues operation depth
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth := by
  intro hschema hvalid hcomplete
  cases depth with
  | zero =>
      intro _state
      exact executeOperationAtDepth_completeNormalizeOperation_depth_zero
        schema store variableValues operation
  | succ depth =>
      intro state
      exact
        executeOperationAtDepth_completeNormalizeOperation_of_recursiveGroupedOperationState
          schema store variableValues operation depth hschema hvalid
          hcomplete state

theorem executeOperationAtDepth_semanticsPreserved_of_recursiveGroupedStoreOperationStateAtDepth
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      recursiveGroupedStoreOperationStateAtDepth schema store variableValues
        operation depth ->
      executeOperationAtDepth schema store variableValues operation depth
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation depth := by
  intro hschema hvalid hcomplete
  cases depth with
  | zero =>
      intro _state
      exact
        executeOperationAtDepth_semanticsPreserved_of_completeNormalizeOperation
          schema store variableValues operation 0 hschema hvalid hcomplete
          (executeOperationAtDepth_completeNormalizeOperation_depth_zero
            schema store variableValues operation)
  | succ depth =>
      intro state
      exact
        executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_recursiveGroupedOperationState
          schema store variableValues operation depth hschema hvalid
          hcomplete state

theorem executeOperationAtDepth_completeNormalizeOperation_of_localFreshPrefixInvariants
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    SelectionSetLocalFreshPrefixInvariants schema (store.resolvers schema)
      variableValues depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hstore hschema hvalid hcomplete invariants hchildren
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_recursiveGroupedOperationState
      schema store variableValues operation depth hschema hvalid hcomplete
      (RecursiveGroupedOperationState.of_localFreshPrefixInvariants
        (rootSourceAppliesBool_store_rootExecutionValue schema store operation
          hstore hvalid)
        invariants hchildren)

theorem executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_localFreshPrefixInvariants
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    SelectionSetLocalFreshPrefixInvariants schema (store.resolvers schema)
      variableValues depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hschema hvalid hcomplete invariants hchildren
  exact
    executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_recursiveGroupedOperationState
      schema store variableValues operation depth hschema hvalid hcomplete
      (RecursiveGroupedOperationState.of_localFreshPrefixInvariants
        (rootSourceAppliesBool_store_rootExecutionValue schema store operation
          hstore hvalid)
        invariants hchildren)

def recursiveGroupedStoreOperationStateAtDepth_of_localFreshPrefixInvariants
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    Validation.operationDefinitionValid schema operation ->
    SelectionSetLocalFreshPrefixInvariants schema (store.resolvers schema)
      variableValues depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      recursiveGroupedStoreOperationStateAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hvalid invariants hchildren
  exact
    RecursiveGroupedOperationState.of_localFreshPrefixInvariants
      (rootSourceAppliesBool_store_rootExecutionValue schema store operation
        hstore hvalid)
      invariants hchildren

def recursiveGroupedStoreOperationStateAtDepth_of_storeFreshPrefixDerivation
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    Validation.operationDefinitionValid schema operation ->
    FreshPrefixSelectionDerivation schema variableValues operation.rootType
      store.rootExecutionValue operation.selectionSet ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      recursiveGroupedStoreOperationStateAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hvalid derivation hchildren
  apply
    recursiveGroupedStoreOperationStateAtDepth_of_localFreshPrefixInvariants
      schema store variableValues operation depth hstore hvalid
  · exact
      SelectionSetLocalFreshPrefixInvariants.of_freshPrefixDerivation
        derivation
        (executionCollectedFieldInvariant_store_root schema store
          variableValues operation depth hstore hvalid)
        (collectedGroupsFieldValidationMergeCompatible_store_root schema
          store variableValues operation depth hstore hvalid)
  · exact hchildren

def recursiveGroupedStoreOperationStateAtDepth_of_freshPlanNormalizes
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    Validation.operationDefinitionValid schema operation ->
    {normalizedSelectionSet : List Selection} ->
    SelectionSetFreshPlanNormalizes schema (store.resolvers schema)
      variableValues depth operation.rootType store.rootExecutionValue
      operation.selectionSet normalizedSelectionSet ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      recursiveGroupedStoreOperationStateAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hvalid _normalizedSelectionSet normalization hchildren
  apply
    recursiveGroupedStoreOperationStateAtDepth_of_localFreshPrefixInvariants
      schema store variableValues operation depth hstore hvalid
  · exact
      { freshFlat := normalization.rawFreshFlat
        collected :=
          executionCollectedFieldInvariant_store_root schema store
            variableValues operation depth hstore hvalid
        compatible :=
          collectedGroupsFieldValidationMergeCompatible_store_root schema store
            variableValues operation depth hstore hvalid }
  · exact hchildren

def recursiveGroupedStoreOperationStateAtDepth_of_freshPlanNormalizationTree
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    Validation.operationDefinitionValid schema operation ->
    {normalizedSelectionSet : List Selection} ->
    SelectionSetFreshPlanNormalizationTree schema (store.resolvers schema)
      variableValues depth operation.rootType store.rootExecutionValue
      operation.selectionSet normalizedSelectionSet ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      recursiveGroupedStoreOperationStateAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hvalid _normalizedSelectionSet normalization hchildren
  exact
    recursiveGroupedStoreOperationStateAtDepth_of_freshPlanNormalizes
      schema store variableValues operation depth hstore hvalid
      normalization.normalizes hchildren

theorem executeOperationAtDepth_completeNormalizeOperation_of_freshPrefixDerivation
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    FreshPrefixSelectionDerivation schema variableValues operation.rootType
      store.rootExecutionValue operation.selectionSet ->
    ExecutionCollectedFieldInvariant
      { window :=
        { schema := schema
          resolvers := store.resolvers schema
          variableValues := variableValues
          depth := depth
          parentType := operation.rootType
          source := store.rootExecutionValue
          selectionSet := operation.selectionSet }
        initial := .object [] } ->
    CollectedGroupsFieldValidationMergeCompatible
      (GraphQL.Execution.collectFields schema variableValues operation.rootType
        store.rootExecutionValue operation.selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hstore hschema hvalid hcomplete derivation collected compatible
    hchildren
  apply executeOperationAtDepth_completeNormalizeOperation_of_localFreshPrefixInvariants
    schema store variableValues operation depth hstore hschema hvalid hcomplete
  · exact
      SelectionSetLocalFreshPrefixInvariants.of_freshPrefixDerivation
        derivation collected compatible
  · exact hchildren

theorem executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_freshPrefixDerivation
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    FreshPrefixSelectionDerivation schema variableValues operation.rootType
      store.rootExecutionValue operation.selectionSet ->
    ExecutionCollectedFieldInvariant
      { window :=
        { schema := schema
          resolvers := store.resolvers schema
          variableValues := variableValues
          depth := depth
          parentType := operation.rootType
          source := store.rootExecutionValue
          selectionSet := operation.selectionSet }
        initial := .object [] } ->
    CollectedGroupsFieldValidationMergeCompatible
      (GraphQL.Execution.collectFields schema variableValues operation.rootType
        store.rootExecutionValue operation.selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hschema hvalid hcomplete derivation collected compatible
    hchildren
  apply
    executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_localFreshPrefixInvariants
      schema store variableValues operation depth hstore hschema hvalid
      hcomplete
  · exact
      SelectionSetLocalFreshPrefixInvariants.of_freshPrefixDerivation
        derivation collected compatible
  · exact hchildren

theorem executeOperationAtDepth_completeNormalizeOperation_of_rootFlat
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    VisitSubfieldsFlatCollects schema (store.resolvers schema) variableValues
      (depth + 1) operation.rootType store.rootExecutionValue
      operation.selectionSet (.object []) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hstore hschema hvalid hcomplete flat hchildren
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_recursiveGroupedOperationState
      schema store variableValues operation depth hschema hvalid hcomplete
      (RecursiveGroupedOperationState.of_localInvariants
        (rootSourceAppliesBool_store_rootExecutionValue schema store operation
          hstore hvalid)
        (selectionSetLocalInvariants_store_root schema store variableValues
          operation depth hstore hvalid flat)
        hchildren)

theorem executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_rootFlat
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    VisitSubfieldsFlatCollects schema (store.resolvers schema) variableValues
      (depth + 1) operation.rootType store.rootExecutionValue
      operation.selectionSet (.object []) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hschema hvalid hcomplete flat hchildren
  exact
    executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_recursiveGroupedOperationState
      schema store variableValues operation depth hschema hvalid hcomplete
      (RecursiveGroupedOperationState.of_localInvariants
        (rootSourceAppliesBool_store_rootExecutionValue schema store operation
          hstore hvalid)
        (selectionSetLocalInvariants_store_root schema store variableValues
          operation depth hstore hvalid flat)
        hchildren)

theorem executeOperationAtDepth_completeNormalizeOperation_of_storeFreshPrefixDerivation
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    FreshPrefixSelectionDerivation schema variableValues operation.rootType
      store.rootExecutionValue operation.selectionSet ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hstore hschema hvalid hcomplete derivation hchildren
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_freshPrefixDerivation
      schema store variableValues operation depth hstore hschema hvalid hcomplete
      derivation
      (executionCollectedFieldInvariant_store_root schema store variableValues
        operation depth hstore hvalid)
      (collectedGroupsFieldValidationMergeCompatible_store_root schema store
        variableValues operation depth hstore hvalid)
      hchildren

theorem executeOperationAtDepth_completeNormalizeOperation_of_freshPlanNormalizationTree
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    {normalizedSelectionSet : List Selection} ->
    SelectionSetFreshPlanNormalizationTree schema (store.resolvers schema)
      variableValues depth operation.rootType store.rootExecutionValue
      operation.selectionSet normalizedSelectionSet ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hstore hschema hvalid hcomplete _normalizedSelectionSet
    normalization hchildren
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_recursiveGroupedStoreOperationStateAtDepth
      schema store variableValues operation (depth + 1) hschema hvalid
      hcomplete
      (recursiveGroupedStoreOperationStateAtDepth_of_freshPlanNormalizationTree
        schema store variableValues operation depth hstore hvalid
        normalization hchildren)

theorem executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_storeFreshPrefixDerivation
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    FreshPrefixSelectionDerivation schema variableValues operation.rootType
      store.rootExecutionValue operation.selectionSet ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hschema hvalid hcomplete derivation hchildren
  exact
    executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_freshPrefixDerivation
      schema store variableValues operation depth hstore hschema hvalid hcomplete
      derivation
      (executionCollectedFieldInvariant_store_root schema store variableValues
        operation depth hstore hvalid)
      (collectedGroupsFieldValidationMergeCompatible_store_root schema store
        variableValues operation depth hstore hvalid)
      hchildren

theorem executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_freshPlanNormalizationTree
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    {normalizedSelectionSet : List Selection} ->
    SelectionSetFreshPlanNormalizationTree schema (store.resolvers schema)
      variableValues depth operation.rootType store.rootExecutionValue
      operation.selectionSet normalizedSelectionSet ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hschema hvalid hcomplete _normalizedSelectionSet
    normalization hchildren
  exact
    executeOperationAtDepth_semanticsPreserved_of_recursiveGroupedStoreOperationStateAtDepth
      schema store variableValues operation (depth + 1) hschema hvalid
      hcomplete
      (recursiveGroupedStoreOperationStateAtDepth_of_freshPlanNormalizationTree
        schema store variableValues operation depth hstore hvalid
        normalization hchildren)

theorem executeOperationAtDepth_completeNormalizeOperation_of_uniqueFieldRoot
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    NormalForm.selectionsAllFields operation.selectionSet ->
    NormalForm.responseNamesNodup operation.selectionSet ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hstore hschema hvalid hcomplete hall hnodup hchildren
  rcases
      SelectionSetFreshPlanNormalizationTree.exists_allFields_responseNamesNodup
        schema (store.resolvers schema) variableValues depth operation.rootType
        store.rootExecutionValue operation.selectionSet hall hnodup with
    ⟨normalizedSelectionSet, hnormalization⟩
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_freshPlanNormalizationTree
      schema store variableValues operation depth hstore hschema hvalid
      hcomplete hnormalization hchildren

theorem executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_uniqueFieldRoot
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    NormalForm.selectionsAllFields operation.selectionSet ->
    NormalForm.responseNamesNodup operation.selectionSet ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hschema hvalid hcomplete hall hnodup hchildren
  rcases
      SelectionSetFreshPlanNormalizationTree.exists_allFields_responseNamesNodup
        schema (store.resolvers schema) variableValues depth operation.rootType
        store.rootExecutionValue operation.selectionSet hall hnodup with
    ⟨normalizedSelectionSet, hnormalization⟩
  exact
    executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_freshPlanNormalizationTree
      schema store variableValues operation depth hstore hschema hvalid
      hcomplete hnormalization hchildren

theorem executeOperationAtDepth_completeNormalizeOperation_of_fieldNormalRoot
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    NormalForm.selectionsAllFields operation.selectionSet ->
    NormalForm.operationDirectiveFree operation ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hstore hschema hvalid hcomplete hall hfree hchildren
  rcases
      SelectionSetFreshPlanNormalizationTree.exists_allFields_directiveFree
        schema (store.resolvers schema) variableValues depth operation.rootType
        store.rootExecutionValue operation.selectionSet hall
        (by simpa [NormalForm.operationDirectiveFree] using hfree) with
    ⟨normalizedSelectionSet, hnormalization⟩
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_freshPlanNormalizationTree
      schema store variableValues operation depth hstore hschema hvalid
      hcomplete hnormalization hchildren

theorem executeOperationAtDepth_completeNormalizeOperation_of_fieldNormalRoot_singletonChildren
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    NormalForm.selectionsAllFields operation.selectionSet ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.responseNamesNodup operation.selectionSet ->
    (∀ responseName field fields,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          field.selectionSet) ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hstore hschema hvalid hcomplete hall hfree hnodup hchildren
  apply executeOperationAtDepth_completeNormalizeOperation_of_fieldNormalRoot
    schema store variableValues operation depth hstore hschema hvalid hcomplete
    hall hfree
  intro responseName field fields prefixTail hgroup hprefix childDepth
    runtimeType identity hlt hinclude
  rcases
      FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_prefix_empty
        schema variableValues operation.rootType store.rootExecutionValue
        operation.selectionSet hall
        (by simpa [NormalForm.operationDirectiveFree] using hfree)
        hnodup hgroup hprefix with
    ⟨_hfields, hprefixTail⟩
  subst prefixTail
  simpa using
    hchildren responseName field fields hgroup childDepth runtimeType identity
      hlt hinclude

theorem executeOperationAtDepth_completeNormalizeOperation_of_fieldNormalRoot_generatedChildren
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    NormalForm.selectionsAllFields operation.selectionSet ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.responseNamesNodup operation.selectionSet ->
    (∀ responseName fieldName arguments directives childSelectionSet,
      Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ operation.selectionSet ->
      generatedNormalizedFieldChild schema
        ((schema.fieldReturnType? operation.rootType fieldName).getD
          fieldName)
        childSelectionSet) ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hstore hschema hvalid hcomplete hall hfree hnodup
    hgeneratedChildren
  apply
    executeOperationAtDepth_completeNormalizeOperation_of_fieldNormalRoot_singletonChildren
      schema store variableValues operation depth hstore hschema hvalid
      hcomplete hall hfree hnodup
  intro responseName field fields hgroup childDepth runtimeType identity hlt
    hinclude
  have hgenerated :
      generatedNormalizedFieldChild schema
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        field.selectionSet :=
    generatedNormalizedFieldChild_of_collectFields_field_layer
      schema variableValues operation.rootType store.rootExecutionValue
      operation.selectionSet hall
      (by simpa [NormalForm.operationDirectiveFree] using hfree)
      hnodup hgeneratedChildren hgroup
      (prefixTail := [])
      (by
        intro candidate hcandidate
        cases hcandidate)
  have hrootApplies :
      rootSourceAppliesBool schema operation store.rootExecutionValue = true :=
    rootSourceAppliesBool_store_rootExecutionValue schema store operation
      hstore hvalid
  have hparentRuntime :
      ScopedParentRuntimeApplies schema store.root.typeName operation.rootType :=
    ScopedParentRuntimeApplies.of_rootSourceAppliesBool schema operation
      store.root.typeName (DataModel.objectRefOfId store.root.id)
      (by simpa [DataModel.Store.rootExecutionValue] using hrootApplies)
  have hrootSelectionValid :
      Validation.selectionSetValid schema operation.variableDefinitions
        operation.rootType operation.selectionSet :=
    Validation.operationDefinitionValid_selectionSetValid hvalid
  have hrootLookup :
      NormalForm.selectionSetLookupValid schema operation.rootType
        operation.selectionSet :=
    NormalForm.selectionSetLookupValid_of_selectionSetValid
      operation.selectionSet hrootSelectionValid
  have hrootImplementation :
      Validation.selectionSetImplementationValidInScope schema
        operation.variableDefinitions operation.rootType operation.selectionSet :=
    (Validation.operationDefinitionValid_selectionSetImplementationValid
      hvalid).1
  have hrootMerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  have hgroupObject :
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues operation.rootType
          (.object store.root.typeName
            (some (DataModel.objectRefOfId store.root.id)))
          operation.selectionSet := by
    simpa [DataModel.Store.rootExecutionValue] using hgroup
  rcases
      collectFields_fieldNormal_childLocalFacts_object schema
        operation.variableDefinitions variableValues operation.rootType
        store.root.typeName
        (some (DataModel.objectRefOfId store.root.id))
        operation.selectionSet responseName runtimeType field fields hschema
        hparentRuntime hrootSelectionValid hrootLookup hrootImplementation
        hrootMerge hall hgroupObject hinclude with
    ⟨hchildLookup, hchildImplementation, hchildMerge⟩
  exact
    recursiveGroupedSelectionSetState_store_object_of_generatedNormalizedFieldChild_recursive
      schema store variableValues childDepth
      ((schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName)
      runtimeType identity field.selectionSet operation.variableDefinitions
      hschema hinclude hgenerated hchildLookup hchildImplementation
      hchildMerge

def recursiveGroupedStoreOperationStateAtDepth_of_fieldNormalRoot_generatedChildren
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.selectionsAllFields operation.selectionSet ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.responseNamesNodup operation.selectionSet ->
    (∀ responseName fieldName arguments directives childSelectionSet,
      Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ operation.selectionSet ->
      generatedNormalizedFieldChild schema
        ((schema.fieldReturnType? operation.rootType fieldName).getD
          fieldName)
        childSelectionSet) ->
      recursiveGroupedStoreOperationStateAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hschema hvalid hall hfree hnodup hgeneratedChildren
  apply
    recursiveGroupedStoreOperationStateAtDepth_of_storeFreshPrefixDerivation
      schema store variableValues operation depth hstore hvalid
  · exact
      FreshPrefixSelectionDerivation.of_allFields_directiveFree_responseNamesNodup
        schema variableValues operation.rootType store.rootExecutionValue
        operation.selectionSet hall
        (by simpa [NormalForm.operationDirectiveFree] using hfree)
        hnodup
  intro responseName field fields prefixTail hgroup hprefix childDepth
    runtimeType identity hlt hinclude
  rcases
      FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_prefix_empty
        schema variableValues operation.rootType store.rootExecutionValue
        operation.selectionSet hall
        (by simpa [NormalForm.operationDirectiveFree] using hfree)
        hnodup hgroup hprefix with
    ⟨_hfields, hprefixTail⟩
  subst prefixTail
  have hgenerated :
      generatedNormalizedFieldChild schema
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        field.selectionSet :=
    generatedNormalizedFieldChild_of_collectFields_field_layer
      schema variableValues operation.rootType store.rootExecutionValue
      operation.selectionSet hall
      (by simpa [NormalForm.operationDirectiveFree] using hfree)
      hnodup hgeneratedChildren hgroup
      (prefixTail := [])
      (by
        intro candidate hcandidate
        cases hcandidate)
  have hrootApplies :
      rootSourceAppliesBool schema operation store.rootExecutionValue = true :=
    rootSourceAppliesBool_store_rootExecutionValue schema store operation
      hstore hvalid
  have hparentRuntime :
      ScopedParentRuntimeApplies schema store.root.typeName operation.rootType :=
    ScopedParentRuntimeApplies.of_rootSourceAppliesBool schema operation
      store.root.typeName (DataModel.objectRefOfId store.root.id)
      (by simpa [DataModel.Store.rootExecutionValue] using hrootApplies)
  have hrootSelectionValid :
      Validation.selectionSetValid schema operation.variableDefinitions
        operation.rootType operation.selectionSet :=
    Validation.operationDefinitionValid_selectionSetValid hvalid
  have hrootLookup :
      NormalForm.selectionSetLookupValid schema operation.rootType
        operation.selectionSet :=
    NormalForm.selectionSetLookupValid_of_selectionSetValid
      operation.selectionSet hrootSelectionValid
  have hrootImplementation :
      Validation.selectionSetImplementationValidInScope schema
        operation.variableDefinitions operation.rootType operation.selectionSet :=
    (Validation.operationDefinitionValid_selectionSetImplementationValid
      hvalid).1
  have hrootMerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  have hgroupObject :
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues operation.rootType
          (.object store.root.typeName
            (some (DataModel.objectRefOfId store.root.id)))
          operation.selectionSet := by
    simpa [DataModel.Store.rootExecutionValue] using hgroup
  rcases
      collectFields_fieldNormal_childLocalFacts_object schema
        operation.variableDefinitions variableValues operation.rootType
        store.root.typeName
        (some (DataModel.objectRefOfId store.root.id))
        operation.selectionSet responseName runtimeType field fields hschema
        hparentRuntime hrootSelectionValid hrootLookup hrootImplementation
        hrootMerge hall hgroupObject hinclude with
    ⟨hchildLookup, hchildImplementation, hchildMerge⟩
  simpa [GraphQL.Execution.mergedFieldSelectionSet] using
    recursiveGroupedSelectionSetState_store_object_of_generatedNormalizedFieldChild_recursive
      schema store variableValues childDepth
      ((schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName)
      runtimeType identity field.selectionSet operation.variableDefinitions
      hschema hinclude hgenerated hchildLookup hchildImplementation
      hchildMerge

theorem executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_fieldNormalRoot
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    NormalForm.selectionsAllFields operation.selectionSet ->
    NormalForm.operationDirectiveFree operation ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : Option DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hschema hvalid hcomplete hall hfree hchildren
  rcases
      SelectionSetFreshPlanNormalizationTree.exists_allFields_directiveFree
        schema (store.resolvers schema) variableValues depth operation.rootType
        store.rootExecutionValue operation.selectionSet hall
        (by simpa [NormalForm.operationDirectiveFree] using hfree) with
    ⟨normalizedSelectionSet, hnormalization⟩
  exact
    executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_freshPlanNormalizationTree
      schema store variableValues operation depth hstore hschema hvalid
      hcomplete hnormalization hchildren

theorem executeOperationAtDepth_completeNormalizeOperation_depth_one_of_storeFreshPrefixDerivation
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    FreshPrefixSelectionDerivation schema variableValues operation.rootType
      store.rootExecutionValue operation.selectionSet ->
      executeOperationAtDepth schema store variableValues operation 1
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) 1 := by
  intro hstore hschema hvalid hcomplete derivation
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_storeFreshPrefixDerivation
      schema store variableValues operation 0 hstore hschema hvalid hcomplete
      derivation
      (by
        intro _responseName _field _fields _prefixTail _hgroup _hprefix
          childDepth _runtimeType _identity hlt _hinclude
        exact False.elim (Nat.not_lt_zero (childDepth + 1) hlt))

theorem executeOperationAtDepth_semanticsPreserved_depth_one_of_storeFreshPrefixDerivation
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    FreshPrefixSelectionDerivation schema variableValues operation.rootType
      store.rootExecutionValue operation.selectionSet ->
      executeOperationAtDepth schema store variableValues operation 1
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation 1 := by
  intro hstore hschema hvalid hcomplete derivation
  exact
    executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_storeFreshPrefixDerivation
      schema store variableValues operation 0 hstore hschema hvalid hcomplete
      derivation
      (by
        intro _responseName _field _fields _prefixTail _hgroup _hprefix
          childDepth _runtimeType _identity hlt _hinclude
        exact False.elim (Nat.not_lt_zero (childDepth + 1) hlt))

theorem executeOperationAtDepth_completeNormalizeOperation_depth_one_of_fieldNormalRoot
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    NormalForm.selectionsAllFields operation.selectionSet ->
    NormalForm.operationDirectiveFree operation ->
      executeOperationAtDepth schema store variableValues operation 1
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) 1 := by
  intro hstore hschema hvalid hcomplete hall hfree
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_fieldNormalRoot
      schema store variableValues operation 0 hstore hschema hvalid hcomplete hall
      hfree
      (by
        intro _responseName _field _fields _prefixTail _hgroup _hprefix
          childDepth _runtimeType _identity hlt _hinclude
        exact False.elim (Nat.not_lt_zero (childDepth + 1) hlt))

theorem executeOperationAtDepth_semanticsPreserved_depth_one_of_fieldNormalRoot
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    NormalForm.selectionsAllFields operation.selectionSet ->
    NormalForm.operationDirectiveFree operation ->
      executeOperationAtDepth schema store variableValues operation 1
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation 1 := by
  intro hstore hschema hvalid hcomplete hall hfree
  exact
    executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_fieldNormalRoot
      schema store variableValues operation 0 hstore hschema hvalid hcomplete hall
      hfree
      (by
        intro _responseName _field _fields _prefixTail _hgroup _hprefix
          childDepth _runtimeType _identity hlt _hinclude
        exact False.elim (Nat.not_lt_zero (childDepth + 1) hlt))

theorem executeOperationAtDepth_completeNormalizeOperation_depth_one_of_normalizeOperation
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.selectionSetsTypeConditionFeasibleInEveryScope schema ->
      executeOperationAtDepth schema store variableValues
          (NormalForm.normalizeOperation schema operation) 1
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema
          (NormalForm.normalizeOperation schema operation)) 1 := by
  intro hstore hschema hvalid hfree hfeasibleAll
  have hnormalizedValid :
      Validation.operationDefinitionValid schema
        (NormalForm.normalizeOperation schema operation) :=
    NormalForm.GroundTypeNormalization.normalizeOperation_valid schema
      operation hschema hvalid hfree hfeasibleAll
  have hnormalizedFree :
      NormalForm.operationDirectiveFree
        (NormalForm.normalizeOperation schema operation) :=
    NormalForm.GroundTypeNormalization.normalizeOperation_directiveFree schema
      operation hfree
  have hcomplete :
      NormalForm.operationBoolVarsComplete
        (NormalForm.normalizeOperation schema operation) variableValues :=
    NormalForm.CompleteNormalization.operationBoolVarsComplete_of_operationDirectiveFree
      (NormalForm.normalizeOperation schema operation) variableValues
      hnormalizedFree
  have hall :
      NormalForm.selectionsAllFields
        (NormalForm.normalizeOperation schema operation).selectionSet := by
    simpa [NormalForm.normalizeOperation] using
      NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
        schema operation.rootType operation.selectionSet
  exact
    executeOperationAtDepth_completeNormalizeOperation_depth_one_of_fieldNormalRoot
      schema store variableValues (NormalForm.normalizeOperation schema operation)
      hstore hschema hnormalizedValid hcomplete hall hnormalizedFree

theorem executeOperationAtDepth_completeNormalizeOperation_of_normalizeOperation_store
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.selectionSetsTypeConditionFeasibleInEveryScope schema ->
      executeOperationAtDepth schema store variableValues
          (NormalForm.normalizeOperation schema operation) depth
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema
          (NormalForm.normalizeOperation schema operation)) depth := by
  intro hstore hschema hvalid hfree hfeasibleAll
  cases depth with
  | zero =>
      exact
        executeOperationAtDepth_completeNormalizeOperation_depth_zero schema
          store variableValues (NormalForm.normalizeOperation schema operation)
  | succ depth =>
      have hnormalizedValid :
          Validation.operationDefinitionValid schema
            (NormalForm.normalizeOperation schema operation) :=
        NormalForm.GroundTypeNormalization.normalizeOperation_valid schema
          operation hschema hvalid hfree hfeasibleAll
      have hnormalizedFree :
          NormalForm.operationDirectiveFree
            (NormalForm.normalizeOperation schema operation) :=
        NormalForm.GroundTypeNormalization.normalizeOperation_directiveFree
          schema operation hfree
      have hcomplete :
          NormalForm.operationBoolVarsComplete
            (NormalForm.normalizeOperation schema operation) variableValues :=
        NormalForm.CompleteNormalization.operationBoolVarsComplete_of_operationDirectiveFree
          (NormalForm.normalizeOperation schema operation) variableValues
          hnormalizedFree
      have hall :
          NormalForm.selectionsAllFields
            (NormalForm.normalizeOperation schema operation).selectionSet := by
        simpa [NormalForm.normalizeOperation] using
          NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
            schema operation.rootType operation.selectionSet
      have hnodup :
          NormalForm.responseNamesNodup
            (NormalForm.normalizeOperation schema operation).selectionSet := by
        simpa [NormalForm.normalizeOperation] using
          NormalForm.GroundTypeNormalization.normalizeSelectionSet_responseNamesNodup
            schema operation.rootType operation.selectionSet
      have hgeneratedChildren :
          ∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives
                childSelectionSet ∈
              (NormalForm.normalizeOperation schema operation).selectionSet ->
            generatedNormalizedFieldChild schema
              ((schema.fieldReturnType?
                    (NormalForm.normalizeOperation schema operation).rootType
                    fieldName).getD fieldName)
              childSelectionSet := by
        intro responseName fieldName arguments directives childSelectionSet
          hmem
        simpa [NormalForm.normalizeOperation] using
          normalizeSelectionSet_field_child_generated schema operation.rootType
            operation.selectionSet responseName fieldName arguments directives
            childSelectionSet
            (by simpa [NormalForm.operationDirectiveFree] using hfree)
            (by simpa [NormalForm.normalizeOperation] using hmem)
      exact
        executeOperationAtDepth_completeNormalizeOperation_of_fieldNormalRoot_generatedChildren
          schema store variableValues
          (NormalForm.normalizeOperation schema operation) depth hstore
          hschema hnormalizedValid hcomplete hall hnormalizedFree hnodup
          hgeneratedChildren

theorem normalizeOperation_completeNormalizationPreservesUngroupedExecution_store
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.selectionSetsTypeConditionFeasibleInEveryScope schema ->
      executeOperationAtDepth schema store variableValues
          (NormalForm.normalizeOperation schema operation) depth
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema
          (NormalForm.normalizeOperation schema operation)) depth := by
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_normalizeOperation_store
      schema store variableValues operation depth

theorem executeOperationAtDepth_completeNormalizeOperation_of_globalFreshPrefixInvariants
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    RecursiveSelectionSetGlobalFreshPrefixInvariants schema
      (store.resolvers schema) variableValues ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hstore hschema hvalid hcomplete hinvariants
  unfold executeOperationAtDepth
  exact
    completeNormalizationPreservesUngroupedExecution_of_globalFreshPrefixInvariants
      schema operation (store.resolvers schema) variableValues depth
      store.rootExecutionValue
      (rootSourceAppliesBool_store_rootExecutionValue schema store operation
        hstore hvalid)
      hinvariants hschema hvalid hcomplete

theorem executeOperationAtDepth_semanticsPreserved_of_globalFreshPrefixInvariants
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    RecursiveSelectionSetGlobalFreshPrefixInvariants schema
      (store.resolvers schema) variableValues ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hschema hvalid hcomplete hinvariants
  unfold executeOperationAtDepth GraphQL.DataModel.executeOperationAtDepth
  exact
    executeQueryAtDepth_semanticsPreserved_of_globalFreshPrefixInvariants
      schema operation (store.resolvers schema) variableValues depth
      store.rootExecutionValue
      (rootSourceAppliesBool_store_rootExecutionValue schema store operation
        hstore hvalid)
      hinvariants hschema hvalid hcomplete

theorem executeOperationAtDepth_completeNormalizeOperation_of_normalizeOperation_via_spec
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.selectionSetsTypeConditionFeasibleInEveryScope schema ->
      executeOperationAtDepth schema store variableValues
          (NormalForm.normalizeOperation schema operation) depth
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema
          (NormalForm.normalizeOperation schema operation)) depth := by
  intro hschema hvalid hfree hfeasibleAll
  unfold executeOperationAtDepth
  exact
    completeNormalizationPreservesUngroupedExecution_of_normalizeOperation
      schema operation (store.resolvers schema) variableValues depth
      store.rootExecutionValue hschema hvalid hfree hfeasibleAll

theorem executeOperationAtDepth_completeNormalizeOperation_of_normalizeOperation
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.selectionSetsTypeConditionFeasibleInEveryScope schema ->
      executeOperationAtDepth schema store variableValues
          (NormalForm.normalizeOperation schema operation) depth
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema
          (NormalForm.normalizeOperation schema operation)) depth := by
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_normalizeOperation_store
      schema store variableValues operation depth

theorem normalizeOperation_completeNormalizationPreservesUngroupedExecution
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.selectionSetsTypeConditionFeasibleInEveryScope schema ->
      executeOperationAtDepth schema store variableValues
          (NormalForm.normalizeOperation schema operation) depth
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema
          (NormalForm.normalizeOperation schema operation)) depth := by
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_normalizeOperation
      schema store variableValues operation depth

theorem normalizeOperation_completeNormalizationPreservesUngroupedExecution_via_spec
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.selectionSetsTypeConditionFeasibleInEveryScope schema ->
      executeOperationAtDepth schema store variableValues
          (NormalForm.normalizeOperation schema operation) depth
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema
          (NormalForm.normalizeOperation schema operation)) depth := by
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_normalizeOperation_via_spec
      schema store variableValues operation depth

theorem executeOperationAtDepth_normalizeThenComplete_semanticsPreserved
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.selectionSetsTypeConditionFeasibleInEveryScope schema ->
      executeOperationAtDepth schema store variableValues
          (NormalForm.completeNormalizeOperation schema
            (NormalForm.normalizeOperation schema operation)) depth
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation depth := by
  intro hschema hvalid hfree hfeasibleAll
  unfold executeOperationAtDepth GraphQL.DataModel.executeOperationAtDepth
  exact
    normalizeThenCompleteUngroupedExecution_semanticsPreserved schema
      operation (store.resolvers schema) variableValues depth
      store.rootExecutionValue hschema hvalid hfree hfeasibleAll

theorem executeOperationAtDepth_normalizeOperation_semanticsPreserved_store
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.selectionSetsTypeConditionFeasibleInEveryScope schema ->
      executeOperationAtDepth schema store variableValues
          (NormalForm.normalizeOperation schema operation) depth
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation depth := by
  intro hstore hschema hvalid hfree hfeasibleAll
  have hcompletePreserved :
      executeOperationAtDepth schema store variableValues
          (NormalForm.normalizeOperation schema operation) depth
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema
          (NormalForm.normalizeOperation schema operation)) depth :=
    executeOperationAtDepth_completeNormalizeOperation_of_normalizeOperation
      schema store variableValues operation depth hstore hschema hvalid hfree
      hfeasibleAll
  have hcompleteSemantics :
      executeOperationAtDepth schema store variableValues
          (NormalForm.completeNormalizeOperation schema
            (NormalForm.normalizeOperation schema operation)) depth
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation depth :=
    executeOperationAtDepth_normalizeThenComplete_semanticsPreserved schema
      store variableValues operation depth hschema hvalid hfree hfeasibleAll
  exact hcompletePreserved.trans hcompleteSemantics

theorem executeOperationAtDepth_normalizeOperation_semanticsPreserved
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.selectionSetsTypeConditionFeasibleInEveryScope schema ->
      executeOperationAtDepth schema store variableValues
          (NormalForm.normalizeOperation schema operation) depth
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation depth := by
  exact
    executeOperationAtDepth_normalizeOperation_semanticsPreserved_store
      schema store variableValues operation depth

theorem completeNormalizeOperation_specExecution_eq_ungroupedExecutionOnData
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
      ∀ store variableValues depth,
        NormalForm.operationBoolVarsComplete operation variableValues ->
          GraphQL.DataModel.executeOperationAtDepth schema store variableValues
              (NormalForm.completeNormalizeOperation schema operation) depth
            =
          executeOperationAtDepth schema store variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth := by
  intro hschema store variableValues depth hcomplete
  exact completeNormalized_specExecution_eq_ungroupedExecution schema store
    variableValues operation depth hschema hcomplete

theorem normalOperation_specExecution_eq_ungroupedExecutionOnData
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.selectionsAllFields operation.selectionSet ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.operationNormal schema operation ->
    (∀ responseName fieldName arguments directives childSelectionSet,
      Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ operation.selectionSet ->
      generatedNormalizedFieldChild schema
        ((schema.fieldReturnType? operation.rootType fieldName).getD
          fieldName)
        childSelectionSet) ->
      ∀ store variableValues depth,
        GraphQL.DataModel.executeOperationAtDepth schema store variableValues
            operation depth
          =
        executeOperationAtDepth schema store variableValues operation depth := by
  intro hschema hall hfree hnormal hchildren store variableValues depth
  exact generatedNormalOperation_specExecution_eq_ungroupedExecution
    schema store variableValues operation depth hschema hall hfree hnormal
    hchildren

theorem normalizeOperation_completeNormalizationPreservesUngroupedExecutionOnData
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.selectionSetsTypeConditionFeasibleInEveryScope schema ->
      ∀ store variableValues depth,
        store.wellTyped schema ->
          executeOperationAtDepth schema store variableValues
              (NormalForm.normalizeOperation schema operation) depth
            =
          executeOperationAtDepth schema store variableValues
            (NormalForm.completeNormalizeOperation schema
              (NormalForm.normalizeOperation schema operation)) depth := by
  intro hschema hvalid hfree hfeasibleAll store variableValues depth hstore
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_normalizeOperation
      schema store variableValues operation depth hstore hschema hvalid hfree
      hfeasibleAll

theorem normalizeOperation_ungroupedExecutionPreservesSpecExecutionOnData
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.selectionSetsTypeConditionFeasibleInEveryScope schema ->
      ∀ store variableValues depth,
        store.wellTyped schema ->
          executeOperationAtDepth schema store variableValues
              (NormalForm.normalizeOperation schema operation) depth
            =
          GraphQL.DataModel.executeOperationAtDepth schema store variableValues
            operation depth := by
  intro hschema hvalid hfree hfeasibleAll store variableValues depth hstore
  exact
    executeOperationAtDepth_normalizeOperation_semanticsPreserved schema store
      variableValues operation depth hstore hschema hvalid hfree hfeasibleAll

theorem normalizedUngroupedExecutionPreservesSpecExecutionOnData
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.selectionSetsTypeConditionFeasibleInEveryScope schema ->
      ∀ store variableValues depth,
        store.wellTyped schema ->
          executeOperationAtDepth schema store variableValues
              (NormalForm.normalizeOperation schema operation) depth
            =
          GraphQL.DataModel.executeOperationAtDepth schema store variableValues
            operation depth := by
  intro hschema hvalid hfree hfeasibleAll store variableValues depth hstore
  have htheorem2 :
      executeOperationAtDepth schema store variableValues
          (NormalForm.normalizeOperation schema operation) depth
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema
          (NormalForm.normalizeOperation schema operation)) depth :=
    normalizeOperation_completeNormalizationPreservesUngroupedExecutionOnData
      schema operation hschema hvalid hfree hfeasibleAll store variableValues
      depth hstore
  have hcomplete :
      executeOperationAtDepth schema store variableValues
          (NormalForm.completeNormalizeOperation schema
            (NormalForm.normalizeOperation schema operation)) depth
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation depth :=
    executeOperationAtDepth_normalizeThenComplete_semanticsPreserved schema
      store variableValues operation depth hschema hvalid hfree hfeasibleAll
  exact htheorem2.trans hcomplete

theorem completeNormalizationPreservesUngroupedExecutionOnData_of_globalFreshPrefixInvariants
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      ∀ store variableValues depth,
        store.wellTyped schema ->
        NormalForm.operationBoolVarsComplete operation variableValues ->
        RecursiveSelectionSetGlobalFreshPrefixInvariants schema
          (store.resolvers schema) variableValues ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          executeOperationAtDepth schema store variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth := by
  intro hschema hvalid store variableValues depth hstore hcomplete
    hinvariants
  cases depth with
  | zero =>
      exact executeOperationAtDepth_completeNormalizeOperation_depth_zero
        schema store variableValues operation
  | succ depth =>
      exact
        executeOperationAtDepth_completeNormalizeOperation_of_globalFreshPrefixInvariants
          schema store variableValues operation depth hstore hschema hvalid
          hcomplete hinvariants

theorem completeNormalizationPreservesUngroupedExecutionOnData_of_flatValidationProvider
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      ∀ store variableValues depth,
        store.wellTyped schema ->
        NormalForm.operationBoolVarsComplete operation variableValues ->
        StoreRecursiveFlatValidationProvider schema store variableValues
          operation.variableDefinitions ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          executeOperationAtDepth schema store variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth := by
  intro hschema hvalid store variableValues depth hstore hcomplete flatProvider
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_recursiveGroupedStoreOperationStateAtDepth
      schema store variableValues operation depth hschema hvalid hcomplete
      (StoreRecursiveFlatValidationProvider.toOperationStateAtDepth
        hschema hstore hvalid flatProvider depth)

theorem completeNormalizationPreservesUngroupedExecutionOnData_of_filter_flatValidationProvider
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      ∀ store variableValues depth,
        store.wellTyped schema ->
        NormalForm.operationBoolVarsComplete operation variableValues ->
        NormalForm.CompleteNormalization.completeBoolCasesCompositeChildrenSurvive
          operation ->
        StoreRecursiveFlatValidationProvider schema store variableValues
          operation.variableDefinitions ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          executeOperationAtDepth schema store variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth := by
  intro hschema hvalid store variableValues depth hstore hcomplete hsurvive
    flatProvider
  cases depth with
  | zero =>
      exact executeOperationAtDepth_completeNormalizeOperation_depth_zero
        schema store variableValues operation
  | succ depth =>
      exact
        executeOperationAtDepth_completeNormalizeOperation_of_filter_flatValidationProvider
          schema store variableValues operation depth hschema hvalid hstore
          hcomplete hsurvive flatProvider

theorem completeNormalizationPreservesUngroupedExecutionOnData_of_normalizationTreeValidationState
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
      ∀ store variableValues depth,
        NormalForm.operationBoolVarsComplete operation variableValues ->
        StoreOperationAtDepthNormalizationTreeValidationState schema store
          variableValues operation depth ->
          executeOperationAtDepth schema store variableValues operation
              (depth + 1)
            =
          executeOperationAtDepth schema store variableValues
            (NormalForm.completeNormalizeOperation schema operation)
            (depth + 1) := by
  intro hschema store variableValues depth hcomplete state
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_normalizationTreeValidationState
      schema store variableValues operation depth hschema hcomplete state

theorem completeNormalizationPreservesUngroupedExecutionOnData_of_filter_freshPlanNormalizes
    (schema : Schema) (operation : Operation) :
      ∀ store variableValues depth,
        NormalForm.operationBoolVarsComplete operation variableValues ->
        (∀ runtimeCase,
          runtimeCase ∈
            NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
          NormalForm.CompleteNormalization.variableValuesAgreeWithCase
            variableValues runtimeCase
            (NormalForm.operationBoolVars operation) ->
          SelectionSetFreshPlanNormalizes schema (store.resolvers schema)
            variableValues depth operation.rootType store.rootExecutionValue
            (NormalForm.filterSelectionSetBoolCase runtimeCase
              operation.selectionSet)
            (NormalForm.normalizeSelectionSet schema operation.rootType
              (NormalForm.filterSelectionSetBoolCase runtimeCase
                operation.selectionSet))) ->
          executeOperationAtDepth schema store variableValues operation
              (depth + 1)
            =
          executeOperationAtDepth schema store variableValues
            (NormalForm.completeNormalizeOperation schema operation)
            (depth + 1) := by
  intro store variableValues depth hcomplete hnormalizes
  unfold executeOperationAtDepth
  exact
    executeQueryAtDepth_completeNormalizeOperation_eq_of_filter_freshPlanNormalizes
      schema operation (store.resolvers schema) variableValues depth
      store.rootExecutionValue hcomplete hnormalizes

theorem completeNormalizationPreservesUngroupedExecutionOnData_of_normalizationTreeValidationInvariants
    (schema : Schema) (operation : Operation) :
    Validation.operationDefinitionValid schema operation ->
      ∀ store variableValues depth,
        store.wellTyped schema ->
        NormalForm.operationBoolVarsComplete operation variableValues ->
        StoreRecursiveNormalizationTreeValidationInvariants schema store
          variableValues operation.variableDefinitions ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          executeOperationAtDepth schema store variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth := by
  intro hvalid store variableValues depth hstore hcomplete invariants
  cases depth with
  | zero =>
      exact executeOperationAtDepth_completeNormalizeOperation_depth_zero
        schema store variableValues operation
  | succ depth =>
      exact
        completeNormalizationPreservesUngroupedExecutionOnData_of_normalizationTreeValidationState
          schema operation invariants.schemaWellFormed store variableValues depth
          hcomplete
          (StoreOperationAtDepthNormalizationTreeValidationState.ofInvariants
            invariants hstore hvalid)

theorem completeNormalizationPreservesUngroupedExecutionOnData_of_rawFreshFlat
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      ∀ store variableValues depth,
        store.wellTyped schema ->
        NormalForm.operationBoolVarsComplete operation variableValues ->
        StoreRecursiveRawFreshFlatValidationProvider schema store
          variableValues operation.variableDefinitions ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          executeOperationAtDepth schema store variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth := by
  intro hschema hvalid store variableValues depth hstore hcomplete freshFlat
  exact
    completeNormalizationPreservesUngroupedExecutionOnData_of_normalizationTreeValidationInvariants
      schema operation hvalid store variableValues depth hstore hcomplete
      (StoreRecursiveNormalizationTreeValidationInvariants.ofRawFreshFlat
        hschema freshFlat)

theorem completeNormalizationPreservesUngroupedExecutionOnData
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      ∀ store variableValues depth,
        store.wellTyped schema ->
        NormalForm.operationBoolVarsComplete operation variableValues ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          executeOperationAtDepth schema store variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth := by
  intro hschema hvalid store variableValues depth hstore hcomplete
  exact
    completeNormalizationPreservesUngroupedExecutionOnData_of_rawFreshFlat
      schema operation hschema hvalid store variableValues depth hstore
      hcomplete
      (storeRecursiveRawFreshFlatValidationProvider schema store
        variableValues operation.variableDefinitions)

theorem completeNormalizationPreservesUngroupedExecutionOnData_iff_semanticsPreserved
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      ((∀ store variableValues depth,
        store.wellTyped schema ->
        NormalForm.operationBoolVarsComplete operation variableValues ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          executeOperationAtDepth schema store variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth)
      ↔
      (∀ store variableValues depth,
        store.wellTyped schema ->
        NormalForm.operationBoolVarsComplete operation variableValues ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          GraphQL.DataModel.executeOperationAtDepth schema store variableValues
            operation depth)) := by
  intro hschema hvalid
  constructor
  · intro hpreserved store variableValues depth hstore hcomplete
    exact
      executeOperationAtDepth_semanticsPreserved_of_completeNormalizeOperation
        schema store variableValues operation depth hschema hvalid hcomplete
        (hpreserved store variableValues depth hstore hcomplete)
  · intro hsemantics store variableValues depth hstore hcomplete
    exact
      executeOperationAtDepth_completeNormalizeOperation_of_semanticsPreserved
        schema store variableValues operation depth hschema hvalid hcomplete
        (hsemantics store variableValues depth hstore hcomplete)

theorem ungroupedExecutionPreservesSpecExecutionOnData_of_completeNormalization
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    (∀ store variableValues depth,
      store.wellTyped schema ->
      NormalForm.operationBoolVarsComplete operation variableValues ->
        executeOperationAtDepth schema store variableValues operation depth
          =
        executeOperationAtDepth schema store variableValues
          (NormalForm.completeNormalizeOperation schema operation) depth) ->
      ∀ store variableValues depth,
        store.wellTyped schema ->
        NormalForm.operationBoolVarsComplete operation variableValues ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          GraphQL.DataModel.executeOperationAtDepth schema store variableValues
            operation depth := by
  intro hschema hvalid hpreserved store variableValues depth hstore
    hcomplete
  exact
    executeOperationAtDepth_semanticsPreserved_of_completeNormalizeOperation
      schema store variableValues operation depth hschema hvalid hcomplete
      (hpreserved store variableValues depth hstore hcomplete)

theorem ungroupedExecutionPreservesSpecExecutionOnData_of_recursiveGroupedStoreOperationStateAtDepth
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      ∀ store variableValues depth,
        NormalForm.operationBoolVarsComplete operation variableValues ->
        recursiveGroupedStoreOperationStateAtDepth schema store variableValues
          operation depth ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          GraphQL.DataModel.executeOperationAtDepth schema store variableValues
            operation depth := by
  intro hschema hvalid store variableValues depth hcomplete state
  exact
    executeOperationAtDepth_semanticsPreserved_of_recursiveGroupedStoreOperationStateAtDepth
      schema store variableValues operation depth hschema hvalid hcomplete
      state

theorem ungroupedExecutionPreservesSpecExecutionOnData_of_globalFreshPrefixInvariants
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      ∀ store variableValues depth,
        store.wellTyped schema ->
        NormalForm.operationBoolVarsComplete operation variableValues ->
        RecursiveSelectionSetGlobalFreshPrefixInvariants schema
          (store.resolvers schema) variableValues ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          GraphQL.DataModel.executeOperationAtDepth schema store variableValues
            operation depth := by
  intro hschema hvalid store variableValues depth hstore hcomplete
    hinvariants
  have hpreserved :
      executeOperationAtDepth schema store variableValues operation depth
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth :=
    completeNormalizationPreservesUngroupedExecutionOnData_of_globalFreshPrefixInvariants
      schema operation hschema hvalid store variableValues depth hstore
      hcomplete hinvariants
  exact
    executeOperationAtDepth_semanticsPreserved_of_completeNormalizeOperation
      schema store variableValues operation depth hschema hvalid hcomplete
      hpreserved

theorem ungroupedExecutionPreservesSpecExecutionOnData_of_flatValidationProvider
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      ∀ store variableValues depth,
        store.wellTyped schema ->
        NormalForm.operationBoolVarsComplete operation variableValues ->
        StoreRecursiveFlatValidationProvider schema store variableValues
          operation.variableDefinitions ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          GraphQL.DataModel.executeOperationAtDepth schema store variableValues
            operation depth := by
  intro hschema hvalid store variableValues depth hstore hcomplete flatProvider
  exact
    executeOperationAtDepth_semanticsPreserved_of_recursiveGroupedStoreOperationStateAtDepth
      schema store variableValues operation depth hschema hvalid hcomplete
      (StoreRecursiveFlatValidationProvider.toOperationStateAtDepth
        hschema hstore hvalid flatProvider depth)

theorem ungroupedExecutionPreservesSpecExecutionOnData_of_filter_flatValidationProvider
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      ∀ store variableValues depth,
        store.wellTyped schema ->
        NormalForm.operationBoolVarsComplete operation variableValues ->
        NormalForm.CompleteNormalization.completeBoolCasesCompositeChildrenSurvive
          operation ->
        StoreRecursiveFlatValidationProvider schema store variableValues
          operation.variableDefinitions ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          GraphQL.DataModel.executeOperationAtDepth schema store variableValues
            operation depth := by
  intro hschema hvalid store variableValues depth hstore hcomplete hsurvive
    flatProvider
  have hpreserved :
      executeOperationAtDepth schema store variableValues operation depth
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth :=
    completeNormalizationPreservesUngroupedExecutionOnData_of_filter_flatValidationProvider
      schema operation hschema hvalid store variableValues depth hstore
      hcomplete hsurvive flatProvider
  exact
    executeOperationAtDepth_semanticsPreserved_of_completeNormalizeOperation
      schema store variableValues operation depth hschema hvalid hcomplete
      hpreserved

theorem ungroupedExecutionPreservesSpecExecutionOnData_of_normalizationTreeValidationState
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
      ∀ store variableValues depth,
        NormalForm.operationBoolVarsComplete operation variableValues ->
        StoreOperationAtDepthNormalizationTreeValidationState schema store
          variableValues operation depth ->
          executeOperationAtDepth schema store variableValues operation
              (depth + 1)
            =
          GraphQL.DataModel.executeOperationAtDepth schema store variableValues
            operation (depth + 1) := by
  intro hschema store variableValues depth hcomplete state
  exact
    executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_normalizationTreeValidationState
      schema store variableValues operation depth hschema hcomplete state

theorem ungroupedExecutionPreservesSpecExecutionOnData_of_normalizationTreeValidationInvariants
    (schema : Schema) (operation : Operation) :
    Validation.operationDefinitionValid schema operation ->
      ∀ store variableValues depth,
        store.wellTyped schema ->
        NormalForm.operationBoolVarsComplete operation variableValues ->
        StoreRecursiveNormalizationTreeValidationInvariants schema store
          variableValues operation.variableDefinitions ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          GraphQL.DataModel.executeOperationAtDepth schema store variableValues
            operation depth := by
  intro hvalid store variableValues depth hstore hcomplete invariants
  have hpreserved :
      executeOperationAtDepth schema store variableValues operation depth
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth :=
    completeNormalizationPreservesUngroupedExecutionOnData_of_normalizationTreeValidationInvariants
      schema operation hvalid store variableValues depth hstore hcomplete
      invariants
  exact
    executeOperationAtDepth_semanticsPreserved_of_completeNormalizeOperation
      schema store variableValues operation depth invariants.schemaWellFormed
      hvalid hcomplete hpreserved

theorem ungroupedExecutionPreservesSpecExecutionOnData_of_rawFreshFlat
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      ∀ store variableValues depth,
        store.wellTyped schema ->
        NormalForm.operationBoolVarsComplete operation variableValues ->
        StoreRecursiveRawFreshFlatValidationProvider schema store
          variableValues operation.variableDefinitions ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          GraphQL.DataModel.executeOperationAtDepth schema store variableValues
            operation depth := by
  intro hschema hvalid store variableValues depth hstore hcomplete freshFlat
  exact
    ungroupedExecutionPreservesSpecExecutionOnData_of_normalizationTreeValidationInvariants
      schema operation hvalid store variableValues depth hstore hcomplete
      (StoreRecursiveNormalizationTreeValidationInvariants.ofRawFreshFlat
        hschema freshFlat)

theorem ungroupedExecutionPreservesSpecExecutionOnData
    (schema : Schema) (operation : Operation) :
    ungroupedExecutionPreservesSpecExecution schema
      operation := by
  intro hschema hvalid store variableValues depth hstore hcomplete
  exact
    ungroupedExecutionPreservesSpecExecutionOnData_of_rawFreshFlat
      schema operation hschema hvalid store variableValues depth hstore
      hcomplete
      (storeRecursiveRawFreshFlatValidationProvider schema store
        variableValues operation.variableDefinitions)

theorem executeOperation_normalizeOperation_semanticsPreservedAtNormalizedDepth
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.selectionSetsTypeConditionFeasibleInEveryScope schema ->
      executeOperation schema store variableValues
          (NormalForm.normalizeOperation schema operation)
        =
      GraphQL.DataModel.executeOperationAtDepth schema store variableValues
        operation
        (GraphQL.Execution.executeQueryDepthBound
          (NormalForm.normalizeOperation schema operation)) := by
  intro hstore hschema hvalid hfree hfeasibleAll
  exact
    executeOperationAtDepth_normalizeOperation_semanticsPreserved schema store
      variableValues operation
      (GraphQL.Execution.executeQueryDepthBound
        (NormalForm.normalizeOperation schema operation))
      hstore hschema hvalid hfree hfeasibleAll

end ExecutionUngrouped

end Algorithms

end GraphQL
