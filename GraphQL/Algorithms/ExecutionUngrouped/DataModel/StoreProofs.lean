import GraphQL.Algorithms.ExecutionUngrouped.DataModel.Wrappers

/-!
Store-backed invariant and semantic-preservation proofs for ungrouped execution.
-/
namespace GraphQL

namespace Algorithms

namespace ExecutionUngrouped

open GraphQL.Execution

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
    (source : ResolverValue DataModel.ObjectRef) :
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
          (Execution.ResolverValue.object store.root.typeName
            (DataModel.objectRefOfId store.root.id)) =
        true := by
    simpa [DataModel.Store.rootExecutionValue] using
      rootSourceAppliesBool_store_rootExecutionValue schema store operation
        hstore hvalid
  simpa [DataModel.Store.rootExecutionValue] using
    ExecutionValidFieldSemanticStateInvariant.of_valid_root_operation_canMerge
      schema (store.resolvers schema) variableValues depth operation
      store.root.typeName (DataModel.objectRefOfId store.root.id)
      (Execution.ResponseValue.object []) hroot hvalid
      (store_resolversRespectValidFieldAndArgumentEquivalence schema store
        (Execution.ResolverValue.object store.root.typeName
          (DataModel.objectRefOfId store.root.id)))

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

theorem executionSelectionSetLookupValid_of_allFields_selectionSetValid
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) (selectionSet : List Selection) :
    NormalForm.selectionsAllFields selectionSet ->
    Validation.selectionSetValid schema variableDefinitions parentType
      selectionSet ->
      executionSelectionSetLookupValid schema parentType selectionSet := by
  intro hall hvalid
  unfold executionSelectionSetLookupValid
  intro selection hmem
  have hfield : Selection.isField selection := hall selection hmem
  have hselectionValid :
      Validation.selectionValid schema variableDefinitions parentType selection := by
    unfold Validation.selectionSetValid at hvalid
    exact hvalid selection hmem
  cases selection with
  | field _responseName fieldName _arguments _directives _selectionSet =>
      rcases Validation.selectionValid_field_lookup hselectionValid with
        ⟨fieldDefinition, hlookup, _harguments, _hchild⟩
      simpa [executionSelectionLookupValid] using ⟨fieldDefinition, hlookup⟩
  | inlineFragment _typeCondition _directives _selectionSet =>
      simp [Selection.isField] at hfield

theorem collectedGroupsFieldLookupValid_store_root_of_allFields
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation) :
    NormalForm.selectionsAllFields operation.selectionSet ->
    Validation.operationDefinitionValid schema operation ->
      CollectedGroupsFieldLookupValid schema operation.rootType
        (GraphQL.Execution.collectFields schema variableValues operation.rootType
          store.rootExecutionValue operation.selectionSet) := by
  intro hall hvalid
  exact
    collectedGroupsFieldLookupValid_of_executionSelectionSetLookupValid
      schema variableValues operation.rootType store.rootExecutionValue
      operation.selectionSet
      (executionSelectionSetLookupValid_of_allFields_selectionSetValid
        schema operation.variableDefinitions operation.rootType operation.selectionSet
        hall
        (Validation.operationDefinitionValid_selectionSetValid hvalid))

def selectionSetLocalInvariants_store_root
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    Validation.operationDefinitionValid schema operation ->
    VisitSubfieldsFlatCollects schema (store.resolvers schema) variableValues
      (depth + 1) operation.rootType store.rootExecutionValue
      operation.selectionSet (.object []) ->
    CollectedGroupsFieldLookupValid schema operation.rootType
      (GraphQL.Execution.collectFields schema variableValues operation.rootType
        store.rootExecutionValue operation.selectionSet) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
    SelectionSetLocalInvariants schema (store.resolvers schema)
      variableValues depth operation.rootType store.rootExecutionValue
      operation.selectionSet := by
  intro hstore hvalid flat hlookups herrors
  exact
    { flat := flat
      collected :=
        executionCollectedFieldInvariant_store_root schema store variableValues
          operation depth hstore hvalid
      compatible :=
        collectedGroupsFieldValidationMergeCompatible_store_root schema store
          variableValues operation depth hstore hvalid
      lookups := hlookups
      errorNeutral := herrors }

theorem executionValidFieldSemanticStateInvariant_store_object_selectionSet_canMerge
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : DataModel.ObjectRef)
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
      runtimeType identity selectionSet (Execution.ResponseValue.object [])
      variableDefinitions hparentRuntime hvalid hmerge
      (store_resolversRespectValidFieldAndArgumentEquivalence schema store
        (Execution.ResolverValue.object runtimeType identity))

theorem executionCollectedFieldInvariant_store_object_selectionSet_canMerge
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : DataModel.ObjectRef)
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
    (parentType runtimeType : Name) (identity : DataModel.ObjectRef)
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
    (parentType runtimeType : Name) (identity : DataModel.ObjectRef)
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
    (parentType runtimeType : Name) (identity : DataModel.ObjectRef)
    (selectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    VisitSubfieldsFlatCollects schema (store.resolvers schema) variableValues
      (depth + 1) parentType (.object runtimeType identity) selectionSet
      (.object []) ->
    ScopedParentRuntimeApplies schema runtimeType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
    CollectedGroupsFieldLookupValid schema parentType
      (GraphQL.Execution.collectFields schema variableValues parentType
        (.object runtimeType identity) selectionSet) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth parentType (.object runtimeType identity) selectionSet ->
    SelectionSetLocalInvariants schema (store.resolvers schema)
      variableValues depth parentType (.object runtimeType identity)
      selectionSet := by
  intro flat hparentRuntime hvalid hmerge hlookups herrors
  exact
    { flat := flat
      collected :=
        executionCollectedFieldInvariant_store_object_selectionSet_canMerge
          schema store variableValues depth parentType runtimeType identity
          selectionSet variableDefinitions hparentRuntime hvalid hmerge
      compatible :=
        collectedGroupsFieldValidationMergeCompatible_store_object_selectionSet_canMerge
          schema store variableValues depth parentType runtimeType identity
          selectionSet variableDefinitions hparentRuntime hvalid hmerge
      lookups := hlookups
      errorNeutral := herrors }

def selectionSetLocalInvariants_store_object_of_groupedFacts
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : DataModel.ObjectRef)
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
    CollectedGroupsFieldLookupValid schema parentType
      (GraphQL.Execution.collectFields schema variableValues parentType
        (.object runtimeType identity) selectionSet) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth parentType (.object runtimeType identity) selectionSet ->
    SelectionSetLocalInvariants schema (store.resolvers schema)
      variableValues depth parentType (.object runtimeType identity)
      selectionSet := by
  intro flat hcompatible hargumentsNodup hlookups herrors
  exact
    { flat := flat
      collected :=
        executionCollectedFieldInvariant_store_object_of_groupedFacts
          schema store variableValues depth parentType runtimeType identity
          selectionSet hcompatible hargumentsNodup
      compatible := hcompatible
      lookups := hlookups
      errorNeutral := herrors }

def selectionSetLocalInvariants_store_object_of_implementationValid
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (collectParent validParent runtimeType : Name)
    (identity : DataModel.ObjectRef)
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
    CollectedGroupsFieldLookupValid schema collectParent
      (GraphQL.Execution.collectFields schema variableValues collectParent
        (.object runtimeType identity) selectionSet) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth collectParent (.object runtimeType identity) selectionSet ->
    SelectionSetLocalInvariants schema (store.resolvers schema)
      variableValues depth collectParent (.object runtimeType identity)
      selectionSet := by
  intro flat hparentRuntime hlookupValid himplementation hmerge hlookups herrors
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
      hlookups
      herrors

def selectionSetLocalFreshPrefixInvariants_store_object_selectionSet_canMerge
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : DataModel.ObjectRef)
    (selectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    FreshPrefixSelectionDerivation schema variableValues parentType
      (.object runtimeType identity) selectionSet ->
    ScopedParentRuntimeApplies schema runtimeType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
    CollectedGroupsFieldLookupValid schema parentType
      (GraphQL.Execution.collectFields schema variableValues parentType
        (.object runtimeType identity) selectionSet) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth parentType (.object runtimeType identity) selectionSet ->
      SelectionSetLocalFreshPrefixInvariants schema (store.resolvers schema)
        variableValues depth parentType (.object runtimeType identity)
        selectionSet := by
  intro derivation hparentRuntime hvalid hmerge hlookups herrors
  exact
    SelectionSetLocalFreshPrefixInvariants.of_freshPrefixDerivation
      derivation
      (executionCollectedFieldInvariant_store_object_selectionSet_canMerge
        schema store variableValues depth parentType runtimeType identity
        selectionSet variableDefinitions hparentRuntime hvalid hmerge)
      (collectedGroupsFieldValidationMergeCompatible_store_object_selectionSet_canMerge
        schema store variableValues depth parentType runtimeType identity
        selectionSet variableDefinitions hparentRuntime hvalid hmerge)
      hlookups
      herrors

def recursiveGroupedSelectionSetState_store_object_selectionSet_canMerge_of_flat
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : DataModel.ObjectRef)
    (selectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    VisitSubfieldsFlatCollects schema (store.resolvers schema) variableValues
      (depth + 1) parentType (.object runtimeType identity) selectionSet
      (.object []) ->
    ScopedParentRuntimeApplies schema runtimeType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
    CollectedGroupsFieldLookupValid schema parentType
      (GraphQL.Execution.collectFields schema variableValues parentType
        (.object runtimeType identity) selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues parentType
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth childRuntime (childIdentity : DataModel.ObjectRef),
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
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues parentType
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childRuntime (childIdentity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          childRuntime = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues childRuntime
          (.object childRuntime childIdentity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth parentType (.object runtimeType identity) selectionSet ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth parentType (.object runtimeType identity)
        selectionSet := by
  intro flat hparentRuntime hvalid hmerge hlookups hchildren hzeroChildren herrors
  exact
    RecursiveGroupedSelectionSetState.of_localInvariants
      (selectionSetLocalInvariants_store_object_selectionSet_canMerge
        schema store variableValues depth parentType runtimeType identity
        selectionSet variableDefinitions flat hparentRuntime hvalid hmerge
        hlookups herrors)
      hchildren hzeroChildren

def recursiveGroupedSelectionSetState_store_object_of_groupedFacts
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : DataModel.ObjectRef)
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
    CollectedGroupsFieldLookupValid schema parentType
      (GraphQL.Execution.collectFields schema variableValues parentType
        (.object runtimeType identity) selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues parentType
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth childRuntime (childIdentity : DataModel.ObjectRef),
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
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues parentType
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childRuntime (childIdentity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          childRuntime = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues childRuntime
          (.object childRuntime childIdentity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth parentType (.object runtimeType identity) selectionSet ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth parentType (.object runtimeType identity)
        selectionSet := by
  intro flat hcompatible hargumentsNodup hlookups hchildren hzeroChildren herrors
  exact
    RecursiveGroupedSelectionSetState.of_localInvariants
      (selectionSetLocalInvariants_store_object_of_groupedFacts
        schema store variableValues depth parentType runtimeType identity
        selectionSet flat hcompatible hargumentsNodup hlookups herrors)
      hchildren hzeroChildren

def recursiveGroupedSelectionSetState_store_object_of_implementationValid
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (collectParent validParent runtimeType : Name)
    (identity : DataModel.ObjectRef)
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
    CollectedGroupsFieldLookupValid schema collectParent
      (GraphQL.Execution.collectFields schema variableValues collectParent
        (.object runtimeType identity) selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues collectParent
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth childRuntime (childIdentity : DataModel.ObjectRef),
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
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues collectParent
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childRuntime (childIdentity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          childRuntime = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues childRuntime
          (.object childRuntime childIdentity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth collectParent (.object runtimeType identity) selectionSet ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth collectParent (.object runtimeType identity)
        selectionSet := by
  intro flat hparentRuntime hlookupValid himplementation hmerge hlookups
    hchildren hzeroChildren herrors
  exact
    RecursiveGroupedSelectionSetState.of_localInvariants
      (selectionSetLocalInvariants_store_object_of_implementationValid
        schema store variableValues depth collectParent validParent runtimeType
        identity selectionSet variableDefinitions flat hparentRuntime
        hlookupValid himplementation hmerge hlookups herrors)
      hchildren hzeroChildren

def recursiveGroupedSelectionSetState_store_object_of_implementationValid_freshPrefixDerivation
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : DataModel.ObjectRef)
    (selectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    FreshPrefixSelectionDerivation schema variableValues parentType
      (.object runtimeType identity) selectionSet ->
    ScopedParentRuntimeApplies schema runtimeType parentType ->
    NormalForm.selectionSetLookupValid schema parentType selectionSet ->
    Validation.selectionSetImplementationValidInScope schema variableDefinitions
      parentType selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
    CollectedGroupsFieldLookupValid schema parentType
      (GraphQL.Execution.collectFields schema variableValues parentType
        (.object runtimeType identity) selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues parentType
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth childRuntime (childIdentity : DataModel.ObjectRef),
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
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues parentType
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childRuntime (childIdentity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          childRuntime = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues childRuntime
          (.object childRuntime childIdentity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth parentType (.object runtimeType identity) selectionSet ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth parentType (.object runtimeType identity)
        selectionSet := by
  intro derivation hparentRuntime hlookupValid himplementation hmerge
    hlookups hchildren hzeroChildren herrors
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
      himplementation hmerge hlookups hchildren hzeroChildren herrors

def recursiveGroupedSelectionSetState_store_object_of_generatedNormalizedFieldChild
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (childType childRuntime : Name)
    (identity : DataModel.ObjectRef)
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
        (grandchildIdentity : DataModel.ObjectRef),
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
      hlookupValid himplementation (hmerge childRuntime)
      (collectedGroupsFieldLookupValid_of_generatedNormalizedFieldChild
        schema variableValues childType childRuntime identity childSelectionSet
        hschema hinclude hgenerated)
      hchildren
      (by
        intro responseName field fields prefixTail hgroup hprefix
          grandchildRuntime grandchildIdentity _hlt hgrandchildInclude
        have hgrandchildGenerated :
            generatedNormalizedFieldChild schema
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              field.selectionSet :=
          generatedNormalizedFieldChild_of_generatedNormalizedFieldChild_collectFields
            schema variableValues childType childRuntime identity
            childSelectionSet hschema hinclude hgenerated hgroup hprefix
        have hprefixTail : prefixTail = [] :=
          (collectFields_generatedNormalizedFieldChild_prefix_empty schema
            variableValues childType childRuntime identity childSelectionSet
            hschema hinclude hgenerated hgroup hprefix).2
        subst prefixTail
        simpa [GraphQL.Execution.mergedFieldSelectionSet] using
          collectedSelectionSetGroupsSingleton_of_generatedNormalizedFieldChild
            schema variableValues
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            grandchildRuntime grandchildIdentity field.selectionSet hschema
            hgrandchildInclude hgrandchildGenerated)
      (by
        intro responseName field fields prefixTail later hgroup hprefix
          hlater grandchildDepth grandchildRuntime grandchildIdentity hlt
        have hprefixTail : prefixTail = [] :=
          (collectFields_generatedNormalizedFieldChild_prefix_empty schema
            variableValues childType childRuntime identity childSelectionSet
            hschema hinclude hgenerated hgroup hprefix).2
        subst prefixTail
        have hfields : fields = [] :=
          (collectFields_generatedNormalizedFieldChild_prefix_empty schema
            variableValues childType childRuntime identity childSelectionSet
            hschema hinclude hgenerated hgroup
            (prefixTail := ([] : List Execution.ExecutableField))
            (by
              intro candidate hmem
              simp at hmem)).1
        subst fields
        simp at hlater)

def recursiveGroupedSelectionSetState_store_object_of_generatedNormalizedFieldChild_singletonChildren
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (childType childRuntime : Name)
    (identity : DataModel.ObjectRef)
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
        (grandchildIdentity : DataModel.ObjectRef),
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
    (identity : DataModel.ObjectRef)
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
    (identity : DataModel.ObjectRef)
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
    executionSelectionSetLookupValid schema collectParent selectionSet ->
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
      ∀ childDepth childRuntime (childIdentity : DataModel.ObjectRef),
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
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues collectParent
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childRuntime (childIdentity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          childRuntime = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues childRuntime
          (.object childRuntime childIdentity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth collectParent (.object runtimeType identity) selectionSet ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth collectParent (.object runtimeType identity)
        selectionSet := by
  intro hschema flat hparentRuntime hvalid hlookupValid himplementation hmerge
    hlookupExec hcompatible hchildren hzeroChildren herrors
  have hlookups :
      CollectedGroupsFieldLookupValid schema collectParent
        (GraphQL.Execution.collectFields schema variableValues collectParent
          (.object runtimeType identity) selectionSet) :=
    collectedGroupsFieldLookupValid_of_executionSelectionSetLookupValid
      schema variableValues collectParent (.object runtimeType identity)
      selectionSet hlookupExec
  apply recursiveGroupedSelectionSetState_store_object_of_implementationValid
    schema store variableValues depth collectParent validParent runtimeType
    identity selectionSet variableDefinitions flat hparentRuntime hlookupValid
    himplementation hmerge hlookups
  · intro responseName field fields prefixTail hgroup hprefix childDepth
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
  · exact hzeroChildren
  · exact herrors

inductive StoreSelectionSetRecursiveNormalizationTreeValidationState
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues)
    (variableDefinitions : List VariableDefinition) :
    Nat -> Name -> Name -> Name -> DataModel.ObjectRef ->
      List Selection -> Type where
  | mk {depth : Nat} {collectParent validParent runtimeType : Name}
      {identity : DataModel.ObjectRef} {selectionSet : List Selection}
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
      (lookups :
        CollectedGroupsFieldLookupValid schema collectParent
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet))
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
      (errorNeutral :
        RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
          depth collectParent (.object runtimeType identity) selectionSet)
      (zeroChildrenSingletons :
        ∀ responseName field fields prefixTail,
          (responseName, field :: fields) ∈
            GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet ->
          (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
          ∀ childRuntime (childIdentity : DataModel.ObjectRef),
            0 < depth ->
            schema.typeIncludesObjectBool
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              childRuntime = true ->
            CollectedSelectionSetGroupsSingleton schema variableValues
              childRuntime (.object childRuntime childIdentity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail)))
      (children :
        ∀ responseName field fields prefixTail,
          (responseName, field :: fields) ∈
            GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet ->
          (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
          ∀ childDepth childRuntime
            (childIdentity : DataModel.ObjectRef),
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
    {identity : DataModel.ObjectRef}
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
    (hlookups :
      CollectedGroupsFieldLookupValid schema collectParent
        (GraphQL.Execution.collectFields schema variableValues collectParent
          (.object runtimeType identity) selectionSet))
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
    (herrors :
      RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
        depth collectParent (.object runtimeType identity) selectionSet)
    (hzeroChildren :
      ∀ responseName field fields prefixTail,
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet ->
        (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
        ∀ childRuntime (childIdentity : DataModel.ObjectRef),
          0 < depth ->
          schema.typeIncludesObjectBool
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            childRuntime = true ->
          CollectedSelectionSetGroupsSingleton schema variableValues childRuntime
            (.object childRuntime childIdentity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail)))
    (hchildren :
      ∀ responseName field fields prefixTail,
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet ->
        (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
        ∀ childDepth childRuntime
          (childIdentity : DataModel.ObjectRef),
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
    hlookups houtputCompatible normalizedSelectionSet hnormalization herrors
    hzeroChildren hchildren

noncomputable def toGroupedState
    {schema : Schema} {store : DataModel.Store}
    {variableValues : VariableValues}
    {variableDefinitions : List VariableDefinition}
    (_hschema : SchemaWellFormedness.schemaWellFormed schema)
    {depth : Nat}
    {collectParent validParent runtimeType : Name}
    {identity : DataModel.ObjectRef}
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
          lookups outputCompatible normalizedSelectionSet normalization
          errorNeutral zeroChildren children =>
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
              parentRuntime lookup implementation merge lookups
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
              zeroChildren
              errorNeutral

end StoreSelectionSetRecursiveNormalizationTreeValidationState

abbrev StoreRecursiveFlatValidationProvider
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues)
    (variableDefinitions : List VariableDefinition) : Prop :=
  ∀ (depth : Nat) (collectParent validParent runtimeType : Name)
    (identity : DataModel.ObjectRef) (selectionSet : List Selection),
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

abbrev StoreRecursiveExecutionLookupProvider
    (schema : Schema) (_store : DataModel.Store)
    (_variableValues : VariableValues)
    (variableDefinitions : List VariableDefinition) : Prop :=
  ∀ (_depth : Nat) (collectParent validParent runtimeType : Name)
    (_identity : DataModel.ObjectRef) (selectionSet : List Selection),
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    collectParent = validParent ->
    schema.objectType validParent ->
    NormalForm.selectionSetLookupValid schema validParent selectionSet ->
    Validation.selectionSetImplementationValidInScope schema
      variableDefinitions validParent selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
      executionSelectionSetLookupValid schema collectParent selectionSet

abbrev StoreRecursiveErrorNeutralProvider
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues)
    (variableDefinitions : List VariableDefinition) : Prop :=
  ∀ (depth : Nat) (collectParent validParent runtimeType : Name)
    (identity : DataModel.ObjectRef) (selectionSet : List Selection),
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    collectParent = validParent ->
    schema.objectType validParent ->
    NormalForm.selectionSetLookupValid schema validParent selectionSet ->
    Validation.selectionSetImplementationValidInScope schema
      variableDefinitions validParent selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
      RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
        depth collectParent (.object runtimeType identity) selectionSet

abbrev StoreRecursiveZeroChildrenSingletonProvider
    (schema : Schema) (_store : DataModel.Store)
    (variableValues : VariableValues)
    (variableDefinitions : List VariableDefinition) : Prop :=
  ∀ (depth : Nat) (collectParent validParent runtimeType : Name)
    (identity : DataModel.ObjectRef) (selectionSet : List Selection),
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    collectParent = validParent ->
    schema.objectType validParent ->
    NormalForm.selectionSetLookupValid schema validParent selectionSet ->
    Validation.selectionSetImplementationValidInScope schema
      variableDefinitions validParent selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
      ∀ responseName field fields prefixTail,
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet ->
        (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
        ∀ childRuntime (childIdentity : DataModel.ObjectRef),
          0 < depth ->
          schema.typeIncludesObjectBool
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            childRuntime = true ->
          CollectedSelectionSetGroupsSingleton schema variableValues childRuntime
            (.object childRuntime childIdentity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))

abbrev StoreRecursiveRawFreshFlatValidationProvider
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues)
    (variableDefinitions : List VariableDefinition) : Prop :=
  ∀ (depth : Nat) (collectParent validParent runtimeType : Name)
    (identity : DataModel.ObjectRef) (selectionSet : List Selection),
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    collectParent = validParent ->
    schema.objectType validParent ->
    NormalForm.selectionSetLookupValid schema validParent selectionSet ->
    Validation.selectionSetImplementationValidInScope schema
      variableDefinitions validParent selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
    executionSelectionSetLookupValid schema collectParent selectionSet ->
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
    (lookupProvider :
      StoreRecursiveExecutionLookupProvider schema store variableValues
        variableDefinitions)
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
      (lookupProvider depth collectParent validParent runtimeType identity
        selectionSet hparentRuntime hparentEq hparentObject hlookup
        himplementation hmerge)
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
    hlookupExec _outputCompatible
  exact
    VisitSubfieldsFlatCollectsFreshPrefixes_all schema (store.resolvers schema)
      variableValues (depth + 1) collectParent
      (.object runtimeType identity) selectionSet hlookupExec

namespace StoreRecursiveFlatValidationProvider

noncomputable def toSelectionSetState
    {schema : Schema} {store : DataModel.Store}
    {variableValues : VariableValues}
    {variableDefinitions : List VariableDefinition}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (flatProvider :
      StoreRecursiveFlatValidationProvider schema store variableValues
        variableDefinitions)
    (lookupProvider :
      StoreRecursiveExecutionLookupProvider schema store variableValues
        variableDefinitions)
    (errorProvider :
      StoreRecursiveErrorNeutralProvider schema store variableValues
        variableDefinitions)
    (zeroChildrenProvider :
      StoreRecursiveZeroChildrenSingletonProvider schema store variableValues
        variableDefinitions) :
    ∀ (depth : Nat) (collectParent validParent runtimeType : Name)
      (identity : DataModel.ObjectRef) (selectionSet : List Selection),
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
      have hlookupExec :
          executionSelectionSetLookupValid schema collectParent selectionSet :=
        lookupProvider depth collectParent validParent runtimeType identity
          selectionSet hparentRuntime hparentEq hparentObject hlookup
          himplementation hmerge
      have hlookups :
          CollectedGroupsFieldLookupValid schema collectParent
            (GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet) :=
        collectedGroupsFieldLookupValid_of_executionSelectionSetLookupValid
          schema variableValues collectParent (.object runtimeType identity)
          selectionSet hlookupExec
      apply
        recursiveGroupedSelectionSetState_store_object_of_implementationValid
          schema store variableValues depth collectParent validParent
          runtimeType identity selectionSet variableDefinitions hflat
          hparentRuntime hlookup himplementation hmerge hlookups
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
      · exact
          zeroChildrenProvider depth collectParent validParent runtimeType
            identity selectionSet hparentRuntime hparentEq hparentObject hlookup
            himplementation hmerge
      · exact
          errorProvider depth collectParent validParent runtimeType identity
            selectionSet hparentRuntime hparentEq hparentObject hlookup
            himplementation hmerge

end StoreRecursiveFlatValidationProvider

structure StoreRecursiveNormalizationTreeValidationInvariants
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues)
    (variableDefinitions : List VariableDefinition) : Type where
  schemaWellFormed : SchemaWellFormedness.schemaWellFormed schema
  lookupValid :
    StoreRecursiveExecutionLookupProvider schema store variableValues
      variableDefinitions
  errorNeutral :
    StoreRecursiveErrorNeutralProvider schema store variableValues
      variableDefinitions
  zeroChildrenSingletons :
    StoreRecursiveZeroChildrenSingletonProvider schema store variableValues
      variableDefinitions
  normalization :
    ∀ (depth : Nat) (collectParent validParent runtimeType : Name)
      (identity : DataModel.ObjectRef) (selectionSet : List Selection),
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
    (lookupValid :
      StoreRecursiveExecutionLookupProvider schema store variableValues
        variableDefinitions)
    (errorNeutral :
      StoreRecursiveErrorNeutralProvider schema store variableValues
        variableDefinitions)
    (zeroChildrenSingletons :
      StoreRecursiveZeroChildrenSingletonProvider schema store variableValues
        variableDefinitions)
    (normalization :
      ∀ (depth : Nat) (collectParent validParent runtimeType : Name)
        (identity : DataModel.ObjectRef) (selectionSet : List Selection),
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
    lookupValid := lookupValid
    errorNeutral := errorNeutral
    zeroChildrenSingletons := zeroChildrenSingletons
    normalization := normalization }

def ofRawFreshFlat
    {schema : Schema} {store : DataModel.Store}
    {variableValues : VariableValues}
    {variableDefinitions : List VariableDefinition}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (lookupValid :
      StoreRecursiveExecutionLookupProvider schema store variableValues
        variableDefinitions)
    (freshFlat :
      StoreRecursiveRawFreshFlatValidationProvider schema store variableValues
        variableDefinitions)
    (errorNeutral :
      StoreRecursiveErrorNeutralProvider schema store variableValues
        variableDefinitions)
    (zeroChildrenSingletons :
      StoreRecursiveZeroChildrenSingletonProvider schema store variableValues
        variableDefinitions) :
    StoreRecursiveNormalizationTreeValidationInvariants schema store
      variableValues variableDefinitions :=
  ofNormalization hschema lookupValid errorNeutral zeroChildrenSingletons
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
              himplementation hmerge
              (lookupValid depth collectParent validParent runtimeType identity
                selectionSet hparentRuntime hparentEq hparentObject hlookup
                himplementation hmerge)
              houtputCompatible)⟩)

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
    hlookupExec houtputCompatible
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
      invariants.schemaWellFormed invariants.lookupValid freshFlat depth
      collectParent validParent runtimeType identity selectionSet hparentRuntime
      hparentEq
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
    (identity : DataModel.ObjectRef) (selectionSet : List Selection)
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
      have hlookupExec :
          executionSelectionSetLookupValid schema collectParent selectionSet :=
        invariants.lookupValid depth collectParent validParent runtimeType
          identity selectionSet hparentRuntime hparentEq hparentObject hlookup
          himplementation hmerge
      have hlookups :
          CollectedGroupsFieldLookupValid schema collectParent
            (GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet) :=
        collectedGroupsFieldLookupValid_of_executionSelectionSetLookupValid
          schema variableValues collectParent (.object runtimeType identity)
          selectionSet hlookupExec
      exact
        mkWithNormalizationChildren hparentRuntime hparentEq hparentObject
          hlookup himplementation hmerge hlookups houtputCompatible
          normalizationWitness.property
          (invariants.errorNeutral depth collectParent validParent runtimeType
            identity selectionSet hparentRuntime hparentEq hparentObject
            hlookup himplementation hmerge)
          (invariants.zeroChildrenSingletons depth collectParent validParent
            runtimeType identity selectionSet hparentRuntime hparentEq
            hparentObject hlookup himplementation hmerge)
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
    (identity : DataModel.ObjectRef)
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
      ∀ childDepth childRuntime (childIdentity : DataModel.ObjectRef),
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
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues parentType
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childRuntime (childIdentity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          childRuntime = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues childRuntime
          (.object childRuntime childIdentity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth parentType (.object runtimeType identity)
        selectionSet := by
  intro hschema flat hparentRuntime hvalid hlookupValid himplementation
    hmerge hall hfree hnodup hchildren hzeroChildren
  have hlookupExec :
      executionSelectionSetLookupValid schema parentType selectionSet :=
    executionSelectionSetLookupValid_of_allFields_selectionSetValid
      schema variableDefinitions parentType selectionSet hall hvalid
  apply
    recursiveGroupedSelectionSetState_store_object_of_implementationValid_childLocalFacts
      schema store variableValues depth parentType parentType runtimeType
      identity selectionSet variableDefinitions hschema flat hparentRuntime
      hvalid hlookupValid himplementation hmerge hlookupExec
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
  · exact hzeroChildren
  · intro responseName field fields prefixTail later hgroup hprefix hlater
      _childDepth _childRuntime _childIdentity _hlt
    rcases
        FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_prefix_empty
          schema variableValues parentType (.object runtimeType identity)
          selectionSet hall hfree hnodup hgroup hprefix with
      ⟨hfields, _hprefixTail⟩
    subst fields
    simp at hlater

def recursiveGroupedSelectionSetState_store_object_of_fieldNormal_generatedChildren
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name)
    (identity : DataModel.ObjectRef)
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
      ∀ childDepth childRuntime (childIdentity : DataModel.ObjectRef),
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
  · intro responseName field fields hgroup childDepth childRuntime childIdentity
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
  · intro responseName field fields prefixTail hgroup hprefix childRuntime
      childIdentity _hlt hinclude
    rcases
        FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_prefix_empty
          schema variableValues parentType (.object runtimeType identity)
          selectionSet hall hfree hnodup hgroup hprefix with
      ⟨_hfields, hprefixTail⟩
    subst prefixTail
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
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      collectedSelectionSetGroupsSingleton_of_generatedNormalizedFieldChild
        schema variableValues
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        childRuntime childIdentity field.selectionSet hschema hinclude
        hgenerated

def recursiveGroupedSelectionSetState_store_object_selectionSet_canMerge
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : DataModel.ObjectRef)
    (selectionSet : List Selection)
    (variableDefinitions : List VariableDefinition) :
    FreshPrefixSelectionDerivation schema variableValues parentType
      (.object runtimeType identity) selectionSet ->
    ScopedParentRuntimeApplies schema runtimeType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
    CollectedGroupsFieldLookupValid schema parentType
      (GraphQL.Execution.collectFields schema variableValues parentType
        (.object runtimeType identity) selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues parentType
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth childRuntime (childIdentity : DataModel.ObjectRef),
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
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues parentType
          (.object runtimeType identity) selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childRuntime (childIdentity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          childRuntime = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues childRuntime
          (.object childRuntime childIdentity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth parentType (.object runtimeType identity) selectionSet ->
      RecursiveGroupedSelectionSetState schema (store.resolvers schema)
        variableValues depth parentType (.object runtimeType identity)
        selectionSet := by
  intro derivation hparentRuntime hvalid hmerge hlookups hchildren
    hzeroChildren herrors
  exact
    RecursiveGroupedSelectionSetState.of_localFreshPrefixInvariants
      (selectionSetLocalFreshPrefixInvariants_store_object_selectionSet_canMerge
        schema store variableValues depth parentType runtimeType identity
        selectionSet variableDefinitions derivation hparentRuntime hvalid hmerge
        hlookups herrors)
      hchildren hzeroChildren

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
    congrArg (fun response => response.data)
      (completeNormalizationPreservesUngroupedExecution_of_recursiveGroupedOperationState
        schema operation (store.resolvers schema) variableValues depth
        store.rootExecutionValue state hschema hvalid hcomplete)

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
      ⟨store.root.typeName, DataModel.objectRefOfId store.root.id,
        ?_, ?_⟩
    · simp [DataModel.Store.rootExecutionValue]
    · exact typeIncludesObjectBool_eq_true_of_typeIncludesObject schema hinclude
  exact
    congrArg (fun response => response.data)
      (executeQueryAtDepth_completeNormalizeOperation_eq_of_filter_recursiveGroupedStates
        schema operation (store.resolvers schema) variableValues depth
        store.rootExecutionValue hschema hcomplete hobject hsource
        (by
          intro runtimeCase _hruntime _hagrees
          exact
            NormalForm.CompleteNormalization.filterSelectionSetBoolCase_directiveFree
              schema runtimeCase operation.selectionSet)
        (by
          intro runtimeCase _hruntime _hagrees
          exact
            NormalForm.CompleteNormalization.filterSelectionSetBoolCase_selectionSetSemanticsReady
              schema runtimeCase operation.rootType operation.selectionSet
              (NormalForm.CompleteNormalization.operation_selectionSetSemanticsReady_of_valid
                hschema hvalid))
        (by
          intro runtimeCase _hruntime _hagrees
          exact
            NormalForm.CompleteNormalization.fieldsInSetCanMerge_filterSelectionSetBoolCase
              schema runtimeCase
              (Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid))
        hstates)

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
    StoreRecursiveExecutionLookupProvider schema store variableValues
      operation.variableDefinitions ->
    StoreRecursiveErrorNeutralProvider schema store variableValues
      operation.variableDefinitions ->
    StoreRecursiveZeroChildrenSingletonProvider schema store variableValues
      operation.variableDefinitions ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation)
        (depth + 1) := by
  intro hschema hvalid hstore hcomplete hsurvive flatProvider lookupProvider
    errorProvider zeroChildrenProvider
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
        flatProvider lookupProvider errorProvider zeroChildrenProvider depth
        operation.rootType operation.rootType store.root.typeName
      (DataModel.objectRefOfId store.root.id)
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
      specExecuteOperationDataAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hschema hvalid hcomplete state
  unfold executeOperationAtDepth specExecuteOperationDataAtDepth
  exact
    congrArg (fun response => response.data)
      (executeQueryAtDepth_semanticsPreserved_via_completeNormalization_of_recursiveGroupedOperationState
        schema operation (store.resolvers schema) variableValues depth
        store.rootExecutionValue state hschema hvalid hcomplete)

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
        operation.variableDefinitions)
    (lookupProvider :
      StoreRecursiveExecutionLookupProvider schema store variableValues
        operation.variableDefinitions)
    (errorProvider :
      StoreRecursiveErrorNeutralProvider schema store variableValues
        operation.variableDefinitions)
    (zeroChildrenProvider :
      StoreRecursiveZeroChildrenSingletonProvider schema store variableValues
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
              hschema flatProvider lookupProvider errorProvider
              zeroChildrenProvider depth operation.rootType operation.rootType
              store.root.typeName
              (DataModel.objectRefOfId store.root.id)
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
      (DataModel.objectRefOfId store.root.id)
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
    (hlookups :
      CollectedGroupsFieldLookupValid schema operation.rootType
        (GraphQL.Execution.collectFields schema variableValues operation.rootType
          store.rootExecutionValue operation.selectionSet))
    (normalizedSelectionSet : List Selection)
    (hnormalization :
      SelectionSetFreshPlanNormalizationTree schema (store.resolvers schema)
        variableValues depth operation.rootType store.rootExecutionValue
        operation.selectionSet normalizedSelectionSet)
    (herrors :
      RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
        depth operation.rootType store.rootExecutionValue
        operation.selectionSet)
    (hzeroChildren :
      ∀ responseName field fields prefixTail,
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues
            operation.rootType store.rootExecutionValue operation.selectionSet ->
        (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
        ∀ childRuntime (childIdentity : DataModel.ObjectRef),
          0 < depth ->
          schema.typeIncludesObjectBool
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            childRuntime = true ->
          CollectedSelectionSetGroupsSingleton schema variableValues childRuntime
            (.object childRuntime childIdentity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail)))
    (hchildren :
      ∀ responseName field fields prefixTail,
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues
            operation.rootType store.rootExecutionValue operation.selectionSet ->
        (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
        ∀ childDepth childRuntime
          (childIdentity : DataModel.ObjectRef),
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
        (by simpa [DataModel.Store.rootExecutionValue] using hlookups)
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
          intro responseName field fields prefixTail later hgroup hprefix
            hlater childDepth childRuntime childIdentity hlt
          exact
            herrors responseName field fields prefixTail later
              (by simpa [DataModel.Store.rootExecutionValue] using hgroup)
              hprefix hlater childDepth childRuntime childIdentity hlt)
        (by
          intro responseName field fields prefixTail hgroup hprefix childRuntime
            childIdentity hlt hinclude
          exact
            hzeroChildren responseName field fields prefixTail
              (by simpa [DataModel.Store.rootExecutionValue] using hgroup)
              hprefix childRuntime childIdentity hlt hinclude)
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
        store.root.typeName (DataModel.objectRefOfId store.root.id)
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
      specExecuteOperationDataAtDepth schema store variableValues
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
       specExecuteOperationDataAtDepth schema store variableValues
        operation depth)) := by
  intro hschema hvalid hcomplete
  have hnormalized :
      executeOperationAtDepth schema store variableValues
          (NormalForm.completeNormalizeOperation schema operation) depth
        =
      specExecuteOperationDataAtDepth schema store variableValues
        operation depth := by
    unfold executeOperationAtDepth specExecuteOperationDataAtDepth
    exact
      congrArg (fun response => response.data)
        (executeQueryAtDepth_completeNormalizeOperation_semanticsPreserved
          schema operation (store.resolvers schema) variableValues depth
          store.rootExecutionValue hschema hvalid hcomplete)
  constructor
  · intro hpreserved
    exact hpreserved.trans hnormalized
  · intro hsemantics
    exact hsemantics.trans hnormalized.symm

theorem specExecuteOperationAtDepth_completeNormalizeOperation_eq_ungrouped
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      specExecuteOperationDataAtDepth schema store variableValues
          (NormalForm.completeNormalizeOperation schema operation) depth
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth := by
  intro hschema hcomplete
  unfold executeOperationAtDepth specExecuteOperationDataAtDepth
  exact
    congrArg (fun response => response.data)
      (specExecution_eq_ungroupedExecution_of_completeNormalizeOperation
        schema operation (store.resolvers schema) variableValues depth
        store.rootExecutionValue hschema hcomplete)

theorem completeNormalized_specExecution_eq_ungroupedExecution
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      specExecuteOperationDataAtDepth schema store variableValues
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
    executionSelectionSetLookupValid schema operation.rootType
      operation.selectionSet ->
    (∀ responseName fieldName arguments directives childSelectionSet,
      Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ operation.selectionSet ->
      generatedNormalizedFieldChild schema
        ((schema.fieldReturnType? operation.rootType fieldName).getD
          fieldName)
        childSelectionSet) ->
      specExecuteOperationDataAtDepth schema store variableValues
          operation depth
        =
        executeOperationAtDepth schema store variableValues operation depth := by
  intro hschema hall hfree hnormal hlookup hchildren
  unfold executeOperationAtDepth specExecuteOperationDataAtDepth
  exact
    congrArg (fun response => response.data)
      ((executeQueryAtDepth_eq_spec_of_generatedNormalOperation schema operation
        (store.resolvers schema) variableValues depth store.rootExecutionValue
        hschema hall hfree hnormal hlookup hchildren).symm)

theorem generatedNormalOperation_specExecution_eq_ungroupedExecution
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.selectionsAllFields operation.selectionSet ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.operationNormal schema operation ->
    executionSelectionSetLookupValid schema operation.rootType
      operation.selectionSet ->
    (∀ responseName fieldName arguments directives childSelectionSet,
      Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ operation.selectionSet ->
      generatedNormalizedFieldChild schema
        ((schema.fieldReturnType? operation.rootType fieldName).getD
          fieldName)
        childSelectionSet) ->
      specExecuteOperationDataAtDepth schema store variableValues
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
      specExecuteOperationDataAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth := by
  intro hschema hcomplete
  exact
    (specExecuteOperationAtDepth_completeNormalizeOperation_eq_ungrouped
      schema store variableValues operation depth hschema hcomplete).symm

theorem executeOperationAtDepth_completeNormalizeOperation_depth_zero
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      executeOperationAtDepth schema store variableValues operation 0
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) 0 := by
  intro hschema hvalid hcomplete
  unfold executeOperationAtDepth
  exact
    (executeQueryAtDepth_data_eq_spec_depth_zero schema (store.resolvers schema)
        variableValues operation store.rootExecutionValue).trans
      (congrArg (fun response => response.data)
        (executeQueryAtDepth_completeNormalizeOperation_semanticsPreserved
          schema operation (store.resolvers schema) variableValues 0
          store.rootExecutionValue hschema hvalid hcomplete).symm)

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
      specExecuteOperationDataAtDepth schema store variableValues
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
    specExecuteOperationDataAtDepth schema store variableValues
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
        schema store variableValues operation hschema hvalid hcomplete
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
      specExecuteOperationDataAtDepth schema store variableValues
        operation depth := by
  intro hschema hvalid hcomplete
  cases depth with
  | zero =>
      intro _state
      exact
        executeOperationAtDepth_semanticsPreserved_of_completeNormalizeOperation
          schema store variableValues operation 0 hschema hvalid hcomplete
          (executeOperationAtDepth_completeNormalizeOperation_depth_zero
            schema store variableValues operation hschema hvalid hcomplete)
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
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          RecursiveGroupedSelectionSetState schema (store.resolvers schema)
            variableValues childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hstore hschema hvalid hcomplete invariants hchildren hzeroChildren
    herrors
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_recursiveGroupedOperationState
      schema store variableValues operation depth hschema hvalid hcomplete
      (RecursiveGroupedOperationState.of_localFreshPrefixInvariants
        (rootSourceAppliesBool_store_rootExecutionValue schema store operation
          hstore hvalid)
        invariants hchildren hzeroChildren)

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
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          RecursiveGroupedSelectionSetState schema (store.resolvers schema)
            variableValues childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      specExecuteOperationDataAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hschema hvalid hcomplete invariants hchildren hzeroChildren
    herrors
  exact
    executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_recursiveGroupedOperationState
      schema store variableValues operation depth hschema hvalid hcomplete
      (RecursiveGroupedOperationState.of_localFreshPrefixInvariants
        (rootSourceAppliesBool_store_rootExecutionValue schema store operation
          hstore hvalid)
        invariants hchildren hzeroChildren)

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
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          RecursiveGroupedSelectionSetState schema (store.resolvers schema)
            variableValues childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
      recursiveGroupedStoreOperationStateAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hvalid invariants hchildren hzeroChildren herrors
  exact
    RecursiveGroupedOperationState.of_localFreshPrefixInvariants
      (rootSourceAppliesBool_store_rootExecutionValue schema store operation
        hstore hvalid)
      invariants hchildren hzeroChildren

def recursiveGroupedStoreOperationStateAtDepth_of_storeFreshPrefixDerivation
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) :
    store.wellTyped schema ->
    Validation.operationDefinitionValid schema operation ->
    FreshPrefixSelectionDerivation schema variableValues operation.rootType
      store.rootExecutionValue operation.selectionSet ->
    CollectedGroupsFieldLookupValid schema operation.rootType
      (GraphQL.Execution.collectFields schema variableValues operation.rootType
        store.rootExecutionValue operation.selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          RecursiveGroupedSelectionSetState schema (store.resolvers schema)
            variableValues childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
      recursiveGroupedStoreOperationStateAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hvalid derivation hlookups hchildren hzeroChildren herrors
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
        hlookups
        herrors
  · exact hchildren
  · exact hzeroChildren
  · exact herrors

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
    CollectedGroupsFieldLookupValid schema operation.rootType
      (GraphQL.Execution.collectFields schema variableValues operation.rootType
        store.rootExecutionValue operation.selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          RecursiveGroupedSelectionSetState schema (store.resolvers schema)
            variableValues childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
      recursiveGroupedStoreOperationStateAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hvalid _normalizedSelectionSet normalization hlookups hchildren
    hzeroChildren herrors
  apply
    recursiveGroupedStoreOperationStateAtDepth_of_localFreshPrefixInvariants
      schema store variableValues operation depth hstore hvalid
  · exact
      { freshFlat := normalization.rawFreshFlat
        collected := (
          executionCollectedFieldInvariant_store_root schema store
            variableValues operation depth hstore hvalid)
        compatible := (
          collectedGroupsFieldValidationMergeCompatible_store_root schema store
            variableValues operation depth hstore hvalid)
        lookups := hlookups
        errorNeutral := herrors }
  · exact hchildren
  · exact hzeroChildren
  · exact herrors

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
    CollectedGroupsFieldLookupValid schema operation.rootType
      (GraphQL.Execution.collectFields schema variableValues operation.rootType
        store.rootExecutionValue operation.selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          RecursiveGroupedSelectionSetState schema (store.resolvers schema)
            variableValues childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
      recursiveGroupedStoreOperationStateAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hvalid _normalizedSelectionSet normalization hlookups hchildren
    hzeroChildren herrors
  exact
    recursiveGroupedStoreOperationStateAtDepth_of_freshPlanNormalizes
      schema store variableValues operation depth hstore hvalid
      normalization.normalizes hlookups hchildren hzeroChildren herrors

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
    CollectedGroupsFieldLookupValid schema operation.rootType
      (GraphQL.Execution.collectFields schema variableValues operation.rootType
        store.rootExecutionValue operation.selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          RecursiveGroupedSelectionSetState schema (store.resolvers schema)
            variableValues childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hstore hschema hvalid hcomplete derivation collected compatible lookups
    hchildren hzeroChildren herrors
  apply executeOperationAtDepth_completeNormalizeOperation_of_localFreshPrefixInvariants
    schema store variableValues operation depth hstore hschema hvalid hcomplete
  · exact
      SelectionSetLocalFreshPrefixInvariants.of_freshPrefixDerivation
        derivation collected compatible lookups herrors
  · exact hchildren
  · exact hzeroChildren
  · exact herrors

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
    CollectedGroupsFieldLookupValid schema operation.rootType
      (GraphQL.Execution.collectFields schema variableValues operation.rootType
        store.rootExecutionValue operation.selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          RecursiveGroupedSelectionSetState schema (store.resolvers schema)
            variableValues childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      specExecuteOperationDataAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hschema hvalid hcomplete derivation collected compatible lookups
    hchildren hzeroChildren herrors
  apply
    executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_localFreshPrefixInvariants
      schema store variableValues operation depth hstore hschema hvalid
      hcomplete
  · exact
      SelectionSetLocalFreshPrefixInvariants.of_freshPrefixDerivation
        derivation collected compatible lookups herrors
  · exact hchildren
  · exact hzeroChildren
  · exact herrors

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
    CollectedGroupsFieldLookupValid schema operation.rootType
      (GraphQL.Execution.collectFields schema variableValues operation.rootType
        store.rootExecutionValue operation.selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          RecursiveGroupedSelectionSetState schema (store.resolvers schema)
            variableValues childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hstore hschema hvalid hcomplete flat hlookups hchildren hzeroChildren
    herrors
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_recursiveGroupedOperationState
      schema store variableValues operation depth hschema hvalid hcomplete
      (RecursiveGroupedOperationState.of_localInvariants
        (rootSourceAppliesBool_store_rootExecutionValue schema store operation
          hstore hvalid)
        (selectionSetLocalInvariants_store_root schema store variableValues
          operation depth hstore hvalid flat hlookups herrors)
        hchildren hzeroChildren)

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
    CollectedGroupsFieldLookupValid schema operation.rootType
      (GraphQL.Execution.collectFields schema variableValues operation.rootType
        store.rootExecutionValue operation.selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          RecursiveGroupedSelectionSetState schema (store.resolvers schema)
            variableValues childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      specExecuteOperationDataAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hschema hvalid hcomplete flat hlookups hchildren hzeroChildren
    herrors
  exact
    executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_recursiveGroupedOperationState
      schema store variableValues operation depth hschema hvalid hcomplete
      (RecursiveGroupedOperationState.of_localInvariants
        (rootSourceAppliesBool_store_rootExecutionValue schema store operation
          hstore hvalid)
        (selectionSetLocalInvariants_store_root schema store variableValues
          operation depth hstore hvalid flat hlookups herrors)
        hchildren hzeroChildren)

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
    CollectedGroupsFieldLookupValid schema operation.rootType
      (GraphQL.Execution.collectFields schema variableValues operation.rootType
        store.rootExecutionValue operation.selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          RecursiveGroupedSelectionSetState schema (store.resolvers schema)
            variableValues childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hstore hschema hvalid hcomplete derivation hlookups hchildren
    hzeroChildren herrors
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_freshPrefixDerivation
      schema store variableValues operation depth hstore hschema hvalid hcomplete
      derivation
      (executionCollectedFieldInvariant_store_root schema store variableValues
        operation depth hstore hvalid)
        (collectedGroupsFieldValidationMergeCompatible_store_root schema store
          variableValues operation depth hstore hvalid)
        hlookups
        hchildren hzeroChildren herrors

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
    CollectedGroupsFieldLookupValid schema operation.rootType
      (GraphQL.Execution.collectFields schema variableValues operation.rootType
        store.rootExecutionValue operation.selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          RecursiveGroupedSelectionSetState schema (store.resolvers schema)
            variableValues childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hstore hschema hvalid hcomplete _normalizedSelectionSet
    normalization hlookups hchildren hzeroChildren herrors
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_recursiveGroupedStoreOperationStateAtDepth
      schema store variableValues operation (depth + 1) hschema hvalid
      hcomplete
        (recursiveGroupedStoreOperationStateAtDepth_of_freshPlanNormalizationTree
          schema store variableValues operation depth hstore hvalid
          normalization hlookups hchildren hzeroChildren herrors)

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
    CollectedGroupsFieldLookupValid schema operation.rootType
      (GraphQL.Execution.collectFields schema variableValues operation.rootType
        store.rootExecutionValue operation.selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          RecursiveGroupedSelectionSetState schema (store.resolvers schema)
            variableValues childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      specExecuteOperationDataAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hschema hvalid hcomplete derivation hlookups hchildren
    hzeroChildren herrors
  exact
    executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_freshPrefixDerivation
      schema store variableValues operation depth hstore hschema hvalid hcomplete
      derivation
      (executionCollectedFieldInvariant_store_root schema store variableValues
        operation depth hstore hvalid)
        (collectedGroupsFieldValidationMergeCompatible_store_root schema store
          variableValues operation depth hstore hvalid)
        hlookups
        hchildren hzeroChildren herrors

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
    CollectedGroupsFieldLookupValid schema operation.rootType
      (GraphQL.Execution.collectFields schema variableValues operation.rootType
        store.rootExecutionValue operation.selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          RecursiveGroupedSelectionSetState schema (store.resolvers schema)
            variableValues childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      specExecuteOperationDataAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hschema hvalid hcomplete _normalizedSelectionSet
    normalization hlookups hchildren hzeroChildren herrors
  exact
    executeOperationAtDepth_semanticsPreserved_of_recursiveGroupedStoreOperationStateAtDepth
      schema store variableValues operation (depth + 1) hschema hvalid
      hcomplete
        (recursiveGroupedStoreOperationStateAtDepth_of_freshPlanNormalizationTree
          schema store variableValues operation depth hstore hvalid
          normalization hlookups hchildren hzeroChildren herrors)

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
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hstore hschema hvalid hcomplete hall hnodup hchildren hzeroChildren
    herrors
  obtain ⟨normalizedSelectionSet, hnormalization⟩ :=
    SelectionSetFreshPlanNormalizationTree.exists_allFields_responseNamesNodup
      schema (store.resolvers schema) variableValues depth operation.rootType
      store.rootExecutionValue operation.selectionSet hall hnodup
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_freshPlanNormalizationTree
      schema store variableValues operation depth hstore hschema hvalid
      hcomplete hnormalization
      (collectedGroupsFieldLookupValid_store_root_of_allFields
        schema store variableValues operation hall hvalid)
      hchildren hzeroChildren herrors

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
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      specExecuteOperationDataAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hschema hvalid hcomplete hall hnodup hchildren hzeroChildren
    herrors
  obtain ⟨normalizedSelectionSet, hnormalization⟩ :=
    SelectionSetFreshPlanNormalizationTree.exists_allFields_responseNamesNodup
      schema (store.resolvers schema) variableValues depth operation.rootType
      store.rootExecutionValue operation.selectionSet hall hnodup
  exact
    executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_freshPlanNormalizationTree
      schema store variableValues operation depth hstore hschema hvalid
      hcomplete hnormalization
      (collectedGroupsFieldLookupValid_store_root_of_allFields
        schema store variableValues operation hall hvalid)
      hchildren hzeroChildren herrors

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
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hstore hschema hvalid hcomplete hall hfree hchildren hzeroChildren
    herrors
  have hlookupExec :
      executionSelectionSetLookupValid schema operation.rootType
        operation.selectionSet :=
    executionSelectionSetLookupValid_of_allFields_selectionSetValid
      schema operation.variableDefinitions operation.rootType
      operation.selectionSet hall
      (Validation.operationDefinitionValid_selectionSetValid hvalid)
  obtain ⟨normalizedSelectionSet, hnormalization⟩ :=
    SelectionSetFreshPlanNormalizationTree.exists_allFields_directiveFree
      schema (store.resolvers schema) variableValues depth operation.rootType
      store.rootExecutionValue operation.selectionSet hall
      (by simpa [NormalForm.operationDirectiveFree] using hfree)
      hlookupExec
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_freshPlanNormalizationTree
      schema store variableValues operation depth hstore hschema hvalid
      hcomplete hnormalization
      (collectedGroupsFieldLookupValid_store_root_of_allFields
        schema store variableValues operation hall hvalid)
      hchildren hzeroChildren herrors

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
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          field.selectionSet) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1) := by
  intro hstore hschema hvalid hcomplete hall hfree hnodup hchildren
    hzeroChildren
  apply executeOperationAtDepth_completeNormalizeOperation_of_fieldNormalRoot
    schema store variableValues operation depth hstore hschema hvalid hcomplete
    hall hfree
  · intro responseName field fields prefixTail hgroup hprefix childDepth
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
  · exact hzeroChildren
  · intro responseName field fields prefixTail later hgroup hprefix hlater
      _childDepth _runtimeType _identity _hlt
    rcases
        FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_prefix_empty
          schema variableValues operation.rootType store.rootExecutionValue
          operation.selectionSet hall
          (by simpa [NormalForm.operationDirectiveFree] using hfree)
          hnodup hgroup hprefix with
      ⟨hfields, _hprefixTail⟩
    subst fields
    simp at hlater

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
            (DataModel.objectRefOfId store.root.id))
          operation.selectionSet := by
    simpa [DataModel.Store.rootExecutionValue] using hgroup
  rcases
      collectFields_fieldNormal_childLocalFacts_object schema
        operation.variableDefinitions variableValues operation.rootType
        store.root.typeName
        (DataModel.objectRefOfId store.root.id)
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
  · intro responseName field fields prefixTail hgroup hprefix runtimeType
      identity _hlt hinclude
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
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      collectedSelectionSetGroupsSingleton_of_generatedNormalizedFieldChild
        schema variableValues
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        runtimeType identity field.selectionSet hschema hinclude hgenerated

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
  · exact
      collectedGroupsFieldLookupValid_store_root_of_allFields
        schema store variableValues operation hall hvalid
  · intro responseName field fields prefixTail hgroup hprefix childDepth
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
              (DataModel.objectRefOfId store.root.id))
            operation.selectionSet := by
      simpa [DataModel.Store.rootExecutionValue] using hgroup
    rcases
        collectFields_fieldNormal_childLocalFacts_object schema
          operation.variableDefinitions variableValues operation.rootType
          store.root.typeName
          (DataModel.objectRefOfId store.root.id)
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
  · intro responseName field fields prefixTail hgroup hprefix runtimeType
      identity _hlt hinclude
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
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      collectedSelectionSetGroupsSingleton_of_generatedNormalizedFieldChild
        schema variableValues
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        runtimeType identity field.selectionSet hschema hinclude hgenerated
  · intro responseName field fields prefixTail later hgroup hprefix hlater
      _childDepth _runtimeType _identity _hlt
    rcases
        FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_prefix_empty
          schema variableValues operation.rootType store.rootExecutionValue
          operation.selectionSet hall
          (by simpa [NormalForm.operationDirectiveFree] using hfree)
          hnodup hgroup hprefix with
      ⟨hfields, _hprefixTail⟩
    subst fields
    simp at hlater

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
      ∀ childDepth runtimeType (identity : DataModel.ObjectRef),
        childDepth + 1 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        RecursiveGroupedSelectionSetState schema (store.resolvers schema)
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    (∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ runtimeType (identity : DataModel.ObjectRef),
        0 < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
        CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail))) ->
    RecursiveErrorNeutralFor schema (store.resolvers schema) variableValues
      depth operation.rootType store.rootExecutionValue
      operation.selectionSet ->
      executeOperationAtDepth schema store variableValues operation (depth + 1)
        =
      specExecuteOperationDataAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hschema hvalid hcomplete hall hfree hchildren hzeroChildren
    herrors
  have hlookupExec :
      executionSelectionSetLookupValid schema operation.rootType
        operation.selectionSet :=
    executionSelectionSetLookupValid_of_allFields_selectionSetValid
      schema operation.variableDefinitions operation.rootType
      operation.selectionSet hall
      (Validation.operationDefinitionValid_selectionSetValid hvalid)
  obtain ⟨normalizedSelectionSet, hnormalization⟩ :=
    SelectionSetFreshPlanNormalizationTree.exists_allFields_directiveFree
      schema (store.resolvers schema) variableValues depth operation.rootType
      store.rootExecutionValue operation.selectionSet hall
      (by simpa [NormalForm.operationDirectiveFree] using hfree)
      hlookupExec
  exact
    executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_freshPlanNormalizationTree
      schema store variableValues operation depth hstore hschema hvalid
      hcomplete hnormalization
      (collectedGroupsFieldLookupValid_store_root_of_allFields
        schema store variableValues operation hall hvalid)
      hchildren hzeroChildren herrors

theorem executeOperationAtDepth_completeNormalizeOperation_depth_one_of_storeFreshPrefixDerivation
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    FreshPrefixSelectionDerivation schema variableValues operation.rootType
      store.rootExecutionValue operation.selectionSet ->
    CollectedGroupsFieldLookupValid schema operation.rootType
      (GraphQL.Execution.collectFields schema variableValues operation.rootType
        store.rootExecutionValue operation.selectionSet) ->
      executeOperationAtDepth schema store variableValues operation 1
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) 1 := by
  intro hstore hschema hvalid hcomplete derivation hlookups
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_storeFreshPrefixDerivation
      schema store variableValues operation 0 hstore hschema hvalid hcomplete
      derivation
      hlookups
      (by
        intro _responseName _field _fields _prefixTail _hgroup _hprefix
          childDepth _runtimeType _identity hlt _hinclude
        exact False.elim (Nat.not_lt_zero (childDepth + 1) hlt))
      (by
        intro _responseName _field _fields _prefixTail _hgroup _hprefix
          _runtimeType _identity hlt _hinclude
        exact False.elim (Nat.not_lt_zero 0 hlt))
      (by
        intro _responseName _field _fields _prefixTail _later _hgroup
          _hprefix _hlater childDepth _runtimeType _identity hlt
        exact False.elim (Nat.not_lt_zero childDepth hlt))

theorem executeOperationAtDepth_semanticsPreserved_depth_one_of_storeFreshPrefixDerivation
    (schema : Schema) (store : DataModel.Store)
    (variableValues : VariableValues) (operation : Operation) :
    store.wellTyped schema ->
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    FreshPrefixSelectionDerivation schema variableValues operation.rootType
      store.rootExecutionValue operation.selectionSet ->
    CollectedGroupsFieldLookupValid schema operation.rootType
      (GraphQL.Execution.collectFields schema variableValues operation.rootType
        store.rootExecutionValue operation.selectionSet) ->
      executeOperationAtDepth schema store variableValues operation 1
        =
      specExecuteOperationDataAtDepth schema store variableValues
        operation 1 := by
  intro hstore hschema hvalid hcomplete derivation hlookups
  exact
    executeOperationAtDepth_semanticsPreserved_via_completeNormalization_of_storeFreshPrefixDerivation
      schema store variableValues operation 0 hstore hschema hvalid hcomplete
      derivation
      hlookups
      (by
        intro _responseName _field _fields _prefixTail _hgroup _hprefix
          childDepth _runtimeType _identity hlt _hinclude
        exact False.elim (Nat.not_lt_zero (childDepth + 1) hlt))
      (by
        intro _responseName _field _fields _prefixTail _hgroup _hprefix
          _runtimeType _identity hlt _hinclude
        exact False.elim (Nat.not_lt_zero 0 hlt))
      (by
        intro _responseName _field _fields _prefixTail _later _hgroup
          _hprefix _hlater childDepth _runtimeType _identity hlt
        exact False.elim (Nat.not_lt_zero childDepth hlt))

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
      (by
        intro _responseName _field _fields _prefixTail _hgroup _hprefix
          _runtimeType _identity hlt _hinclude
        exact False.elim (Nat.not_lt_zero 0 hlt))
      (by
        intro _responseName _field _fields _prefixTail _later _hgroup
          _hprefix _hlater childDepth _runtimeType _identity hlt
        exact False.elim (Nat.not_lt_zero childDepth hlt))

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
      specExecuteOperationDataAtDepth schema store variableValues
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
      (by
        intro _responseName _field _fields _prefixTail _hgroup _hprefix
          _runtimeType _identity hlt _hinclude
        exact False.elim (Nat.not_lt_zero 0 hlt))
      (by
        intro _responseName _field _fields _prefixTail _later _hgroup
          _hprefix _hlater childDepth _runtimeType _identity hlt
        exact False.elim (Nat.not_lt_zero childDepth hlt))

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
      exact
        executeOperationAtDepth_completeNormalizeOperation_depth_zero schema
          store variableValues (NormalForm.normalizeOperation schema operation)
          hschema hnormalizedValid hcomplete
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
    congrArg (fun response => response.data)
      (completeNormalizationPreservesUngroupedExecution_of_globalFreshPrefixInvariants
        schema operation (store.resolvers schema) variableValues depth
        store.rootExecutionValue
        (rootSourceAppliesBool_store_rootExecutionValue schema store operation
          hstore hvalid)
        hinvariants hschema hvalid hcomplete)

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
      specExecuteOperationDataAtDepth schema store variableValues
        operation (depth + 1) := by
  intro hstore hschema hvalid hcomplete hinvariants
  unfold executeOperationAtDepth specExecuteOperationDataAtDepth
  exact
    congrArg (fun response => response.data)
      (executeQueryAtDepth_semanticsPreserved_of_globalFreshPrefixInvariants
        schema operation (store.resolvers schema) variableValues depth
        store.rootExecutionValue
        (rootSourceAppliesBool_store_rootExecutionValue schema store operation
          hstore hvalid)
        hinvariants hschema hvalid hcomplete)

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
    congrArg (fun response => response.data)
      (completeNormalizationPreservesUngroupedExecution_of_normalizeOperation
        schema operation (store.resolvers schema) variableValues depth
        store.rootExecutionValue hschema hvalid hfree hfeasibleAll)

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
      specExecuteOperationDataAtDepth schema store variableValues
        operation depth := by
  intro hschema hvalid hfree hfeasibleAll
  unfold executeOperationAtDepth specExecuteOperationDataAtDepth
  exact
    congrArg (fun response => response.data)
      (normalizeThenCompleteUngroupedExecution_semanticsPreserved schema
        operation (store.resolvers schema) variableValues depth
        store.rootExecutionValue hschema hvalid hfree hfeasibleAll)

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
      specExecuteOperationDataAtDepth schema store variableValues
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
      specExecuteOperationDataAtDepth schema store variableValues
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
      specExecuteOperationDataAtDepth schema store variableValues
        operation depth := by
  exact
    executeOperationAtDepth_normalizeOperation_semanticsPreserved_store
      schema store variableValues operation depth

theorem completeNormalizeOperation_specExecution_eq_ungroupedExecutionOnData
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
      ∀ store variableValues depth,
        NormalForm.operationBoolVarsComplete operation variableValues ->
          specExecuteOperationDataAtDepth schema store variableValues
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
    executionSelectionSetLookupValid schema operation.rootType
      operation.selectionSet ->
    (∀ responseName fieldName arguments directives childSelectionSet,
      Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ operation.selectionSet ->
      generatedNormalizedFieldChild schema
        ((schema.fieldReturnType? operation.rootType fieldName).getD
          fieldName)
        childSelectionSet) ->
      ∀ store variableValues depth,
        specExecuteOperationDataAtDepth schema store variableValues
            operation depth
          =
          executeOperationAtDepth schema store variableValues operation depth := by
  intro hschema hall hfree hnormal hlookup hchildren store variableValues depth
  exact generatedNormalOperation_specExecution_eq_ungroupedExecution
    schema store variableValues operation depth hschema hall hfree hnormal
    hlookup hchildren

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
          specExecuteOperationDataAtDepth schema store variableValues
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
          specExecuteOperationDataAtDepth schema store variableValues
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
      specExecuteOperationDataAtDepth schema store variableValues
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
        schema store variableValues operation hschema hvalid hcomplete
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
        StoreRecursiveExecutionLookupProvider schema store variableValues
          operation.variableDefinitions ->
        StoreRecursiveErrorNeutralProvider schema store variableValues
          operation.variableDefinitions ->
        StoreRecursiveZeroChildrenSingletonProvider schema store variableValues
          operation.variableDefinitions ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          executeOperationAtDepth schema store variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth := by
  intro hschema hvalid store variableValues depth hstore hcomplete flatProvider
    lookupProvider errorProvider zeroChildrenProvider
  exact
    executeOperationAtDepth_completeNormalizeOperation_of_recursiveGroupedStoreOperationStateAtDepth
      schema store variableValues operation depth hschema hvalid hcomplete
        (StoreRecursiveFlatValidationProvider.toOperationStateAtDepth
          hschema hstore hvalid flatProvider lookupProvider errorProvider
          zeroChildrenProvider depth)

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
        StoreRecursiveExecutionLookupProvider schema store variableValues
          operation.variableDefinitions ->
        StoreRecursiveErrorNeutralProvider schema store variableValues
          operation.variableDefinitions ->
        StoreRecursiveZeroChildrenSingletonProvider schema store variableValues
          operation.variableDefinitions ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          executeOperationAtDepth schema store variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth := by
  intro hschema hvalid store variableValues depth hstore hcomplete hsurvive
    flatProvider lookupProvider errorProvider zeroChildrenProvider
  cases depth with
  | zero =>
      exact executeOperationAtDepth_completeNormalizeOperation_depth_zero
        schema store variableValues operation hschema hvalid hcomplete
  | succ depth =>
      exact
        executeOperationAtDepth_completeNormalizeOperation_of_filter_flatValidationProvider
            schema store variableValues operation depth hschema hvalid hstore
            hcomplete hsurvive flatProvider lookupProvider errorProvider
            zeroChildrenProvider

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
    congrArg (fun response => response.data)
      (executeQueryAtDepth_completeNormalizeOperation_eq_of_filter_freshPlanNormalizes
        schema operation (store.resolvers schema) variableValues depth
        store.rootExecutionValue hcomplete hnormalizes)

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
        schema store variableValues operation invariants.schemaWellFormed hvalid
        hcomplete
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
        StoreRecursiveExecutionLookupProvider schema store variableValues
          operation.variableDefinitions ->
        StoreRecursiveErrorNeutralProvider schema store variableValues
          operation.variableDefinitions ->
        StoreRecursiveZeroChildrenSingletonProvider schema store variableValues
          operation.variableDefinitions ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          executeOperationAtDepth schema store variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth := by
  intro hschema hvalid store variableValues depth hstore hcomplete freshFlat
    lookupProvider errorProvider zeroChildrenProvider
  exact
    completeNormalizationPreservesUngroupedExecutionOnData_of_normalizationTreeValidationInvariants
      schema operation hvalid store variableValues depth hstore hcomplete
        (StoreRecursiveNormalizationTreeValidationInvariants.ofRawFreshFlat
          hschema lookupProvider freshFlat errorProvider zeroChildrenProvider)

theorem completeNormalizationPreservesUngroupedExecutionOnData
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      ∀ store variableValues depth,
        store.wellTyped schema ->
        NormalForm.operationBoolVarsComplete operation variableValues ->
        StoreRecursiveExecutionLookupProvider schema store variableValues
          operation.variableDefinitions ->
        StoreRecursiveErrorNeutralProvider schema store variableValues
          operation.variableDefinitions ->
        StoreRecursiveZeroChildrenSingletonProvider schema store variableValues
          operation.variableDefinitions ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          executeOperationAtDepth schema store variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth := by
  intro hschema hvalid store variableValues depth hstore hcomplete lookupProvider
    errorProvider zeroChildrenProvider
  exact
    completeNormalizationPreservesUngroupedExecutionOnData_of_rawFreshFlat
      schema operation hschema hvalid store variableValues depth hstore
      hcomplete
      (storeRecursiveRawFreshFlatValidationProvider schema store
        variableValues operation.variableDefinitions)
      lookupProvider
      errorProvider zeroChildrenProvider

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
          specExecuteOperationDataAtDepth schema store variableValues
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
          specExecuteOperationDataAtDepth schema store variableValues
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
          specExecuteOperationDataAtDepth schema store variableValues
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
          specExecuteOperationDataAtDepth schema store variableValues
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
        StoreRecursiveExecutionLookupProvider schema store variableValues
          operation.variableDefinitions ->
        StoreRecursiveErrorNeutralProvider schema store variableValues
          operation.variableDefinitions ->
        StoreRecursiveZeroChildrenSingletonProvider schema store variableValues
          operation.variableDefinitions ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          specExecuteOperationDataAtDepth schema store variableValues
            operation depth := by
  intro hschema hvalid store variableValues depth hstore hcomplete flatProvider
    lookupProvider errorProvider zeroChildrenProvider
  exact
    executeOperationAtDepth_semanticsPreserved_of_recursiveGroupedStoreOperationStateAtDepth
      schema store variableValues operation depth hschema hvalid hcomplete
        (StoreRecursiveFlatValidationProvider.toOperationStateAtDepth
          hschema hstore hvalid flatProvider lookupProvider errorProvider
          zeroChildrenProvider depth)

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
        StoreRecursiveExecutionLookupProvider schema store variableValues
          operation.variableDefinitions ->
        StoreRecursiveErrorNeutralProvider schema store variableValues
          operation.variableDefinitions ->
        StoreRecursiveZeroChildrenSingletonProvider schema store variableValues
          operation.variableDefinitions ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          specExecuteOperationDataAtDepth schema store variableValues
            operation depth := by
  intro hschema hvalid store variableValues depth hstore hcomplete hsurvive
    flatProvider lookupProvider errorProvider zeroChildrenProvider
  have hpreserved :
      executeOperationAtDepth schema store variableValues operation depth
        =
      executeOperationAtDepth schema store variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth :=
      completeNormalizationPreservesUngroupedExecutionOnData_of_filter_flatValidationProvider
        schema operation hschema hvalid store variableValues depth hstore
        hcomplete hsurvive flatProvider lookupProvider errorProvider
        zeroChildrenProvider
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
          specExecuteOperationDataAtDepth schema store variableValues
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
          specExecuteOperationDataAtDepth schema store variableValues
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
        StoreRecursiveExecutionLookupProvider schema store variableValues
          operation.variableDefinitions ->
        StoreRecursiveErrorNeutralProvider schema store variableValues
          operation.variableDefinitions ->
        StoreRecursiveZeroChildrenSingletonProvider schema store variableValues
          operation.variableDefinitions ->
          executeOperationAtDepth schema store variableValues operation depth
            =
          specExecuteOperationDataAtDepth schema store variableValues
            operation depth := by
  intro hschema hvalid store variableValues depth hstore hcomplete freshFlat
    lookupProvider errorProvider zeroChildrenProvider
  exact
    ungroupedExecutionPreservesSpecExecutionOnData_of_normalizationTreeValidationInvariants
      schema operation hvalid store variableValues depth hstore hcomplete
        (StoreRecursiveNormalizationTreeValidationInvariants.ofRawFreshFlat
          hschema lookupProvider freshFlat errorProvider zeroChildrenProvider)

theorem ungroupedExecutionPreservesSpecExecution_of_globalFreshPrefixInvariants
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      ∀ store variableValues depth,
        store.wellTyped schema ->
        NormalForm.operationBoolVarsComplete operation variableValues ->
        CollectedSelectionSetGroupsSingleton schema variableValues
          operation.rootType store.rootExecutionValue operation.selectionSet ->
        RecursiveSelectionSetGlobalFreshPrefixInvariants schema
          (store.resolvers schema) variableValues ->
          executeOperationResponseAtDepth schema store variableValues
            operation depth
            =
          specExecuteOperationAtDepth schema store variableValues
            operation depth := by
  intro hschema hvalid store variableValues depth hstore hcomplete
    hrootSingleton hinvariants
  unfold executeOperationResponseAtDepth specExecuteOperationAtDepth
  unfold GraphQL.DataModel.executeOperationAtDepth
  cases depth with
  | zero =>
      exact executeQueryAtDepth_eq_spec_depth_zero schema operation
        (store.resolvers schema) variableValues store.rootExecutionValue
        hrootSingleton
  | succ depth =>
      exact
        executeQueryAtDepth_semanticsPreserved_of_globalFreshPrefixInvariants
          schema operation (store.resolvers schema) variableValues depth
          store.rootExecutionValue
          (rootSourceAppliesBool_store_rootExecutionValue schema store operation
            hstore hvalid)
          hinvariants
          hschema hvalid hcomplete

theorem ungroupedExecutionPreservesSpecExecutionOnData
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
          specExecuteOperationDataAtDepth schema store variableValues
            operation depth := by
  intro hschema hvalid store variableValues depth hstore hcomplete
    hinvariants
  exact
    ungroupedExecutionPreservesSpecExecutionOnData_of_globalFreshPrefixInvariants
      schema operation hschema hvalid store variableValues depth hstore
      hcomplete hinvariants

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
      specExecuteOperationDataAtDepth schema store variableValues
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
