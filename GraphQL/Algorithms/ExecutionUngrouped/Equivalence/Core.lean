import GraphQL.Algorithms.ExecutionUngrouped
import GraphQL.NormalForm.Shared.Execution
import GraphQL.NormalForm.Shared.FieldMerge
import GraphQL.NormalForm.Shared.RuntimeTypes
import GraphQL.SchemaWellFormedness.PossibleTypes
import GraphQL.Validation.FieldMerge
import GraphQL.Validation.SelectionValidity

/-!
Proof-facing scaffolding for relating direct ungrouped execution to the grouped
spec execution in `GraphQL.Execution`.

The final equivalence theorem is intended for valid operations over stable data:
validation rules rule out invalid alias collisions, and the data model supplies the
assumption that repeated field visits for the same response key resolve the same source
data. The algorithm itself remains operationally direct and may call resolvers more
often than the grouped spec; equivalence is about the public response data.
-/
namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution
structure ExecutionWindow (ObjectIdentity : Type) where
  schema : Schema
  resolvers : Resolvers ObjectIdentity
  variableValues : VariableValues
  depth : Nat
  parentType : Name
  source : Value ObjectIdentity
  selectionSet : List Selection

namespace ExecutionWindow

def ungroupedResponseFields (window : ExecutionWindow ObjectIdentity) :
    List (Name × Response) :=
  executeRootSelectionSet window.schema window.resolvers window.variableValues
    window.depth window.parentType window.source window.selectionSet

def specResponseFields (window : ExecutionWindow ObjectIdentity) :
    List (Name × Response) :=
  GraphQL.Execution.executeRootSelectionSet window.schema window.resolvers
    window.variableValues window.depth window.parentType window.source
    window.selectionSet

def ungroupedResponse (window : ExecutionWindow ObjectIdentity) : Response :=
  .object window.ungroupedResponseFields

def specResponse (window : ExecutionWindow ObjectIdentity) : Response :=
  .object window.specResponseFields

end ExecutionWindow

structure ExecutionEquivalenceState (ObjectIdentity : Type) where
  window : ExecutionWindow ObjectIdentity
  initial : Response

namespace ExecutionEquivalenceState

def ungroupedProjection (state : ExecutionEquivalenceState ObjectIdentity) :
    Response :=
  visitSubfields state.window.schema state.window.resolvers
    state.window.variableValues state.window.depth state.window.parentType
    state.window.source state.window.selectionSet state.initial

def specProjection (state : ExecutionEquivalenceState ObjectIdentity) :
    Response :=
  mergeResponse state.initial
    (.object
      (GraphQL.Execution.executeCollectedFields state.window.schema
        state.window.resolvers state.window.variableValues state.window.depth
        state.window.source
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet)))

end ExecutionEquivalenceState

def ResponseDataEquivalent (left right : Response) : Prop :=
  left = right

def ResponseAbsorbs (base output : Response) : Prop :=
  mergeResponse base output = output

def ExecutionWindowEquivalent (window : ExecutionWindow ObjectIdentity) : Prop :=
  ResponseDataEquivalent window.ungroupedResponse window.specResponse

def ExecutionStateEquivalent
    (state : ExecutionEquivalenceState ObjectIdentity) : Prop :=
  ResponseDataEquivalent state.ungroupedProjection state.specProjection

def PairKeysNodup {α : Type} (fields : List (Name × α)) : Prop :=
  (fields.map Prod.fst).Nodup

theorem PairKeysNodup.tail
    {α : Type} {head : Name × α} {rest : List (Name × α)} :
    PairKeysNodup (head :: rest) ->
      PairKeysNodup rest := by
  intro hnodup
  rcases head with ⟨_, _⟩
  unfold PairKeysNodup at hnodup ⊢
  exact (List.nodup_cons.mp hnodup).2

theorem PairKeysNodup.head_not_mem_tail
    {α : Type} {responseName : Name} {value : α}
    {rest : List (Name × α)} :
    PairKeysNodup ((responseName, value) :: rest) ->
      responseName ∉ rest.map Prod.fst := by
  intro hnodup
  unfold PairKeysNodup at hnodup
  exact (List.nodup_cons.mp hnodup).1

theorem executableGroupNamesDisjoint_singleton_tail_of_pairKeysNodup
    {responseName : Name} {fields : List ExecutableField}
    {rest : List (Name × List ExecutableField)} :
    PairKeysNodup ((responseName, fields) :: rest) ->
      NormalForm.executableGroupNamesDisjoint [(responseName, fields)] rest := by
  intro hnodup candidate hleft hright
  have hcandidate : candidate = responseName := by
    simpa using hleft
  subst candidate
  exact PairKeysNodup.head_not_mem_tail hnodup hright

theorem executableGroupNamesNodup_of_pairKeysNodup
    (groups : List (Name × List ExecutableField)) :
    PairKeysNodup groups ->
      NormalForm.executableGroupNamesNodup groups := by
  induction groups with
  | nil =>
      simp [PairKeysNodup, NormalForm.executableGroupNamesNodup]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      intro hnodup
      have hparts :
          responseName ∉ rest.map Prod.fst ∧ PairKeysNodup rest := by
        unfold PairKeysNodup at hnodup ⊢
        exact List.nodup_cons.mp hnodup
      exact ⟨hparts.1, ih hparts.2⟩

theorem PairKeysNodup_of_executableGroupNamesNodup
    (groups : List (Name × List ExecutableField)) :
    NormalForm.executableGroupNamesNodup groups ->
      PairKeysNodup groups := by
  induction groups with
  | nil =>
      simp [PairKeysNodup]
  | cons group rest ih =>
      cases group with
      | mk responseName fields =>
          intro hnodup
          unfold NormalForm.executableGroupNamesNodup at hnodup
          unfold PairKeysNodup
          exact List.nodup_cons.mpr ⟨hnodup.1, ih hnodup.2⟩

inductive ResponseMergeReady : Response -> Prop where
  | null : ResponseMergeReady .null
  | scalar (value : String) : ResponseMergeReady (.scalar value)
  | object (fields : List (Name × Response)) :
      PairKeysNodup fields ->
      (∀ responseName response,
        (responseName, response) ∈ fields ->
          ResponseMergeReady response) ->
        ResponseMergeReady (.object fields)
  | list (values : List Response) :
      (∀ response,
        response ∈ values ->
          ResponseMergeReady response) ->
        ResponseMergeReady (.list values)

def MergeResponseFieldsReadySteps :
    List (Name × Response) -> List (Name × Response) -> Prop
  | _existing, [] => True
  | existing, (responseName, incoming)::rest =>
      ResponseMergeReady incoming ∧
      (∀ existingResponse,
        (responseName, existingResponse) ∈ existing ->
          ResponseMergeReady (mergeResponse existingResponse incoming)) ∧
      MergeResponseFieldsReadySteps
        (mergeResponseField responseName incoming existing) rest

def MergeResponseFieldsAbsorbsFrom
    (base : List (Name × Response)) :
    List (Name × Response) -> List (Name × Response) -> Prop
  | current, [] => ResponseAbsorbs (.object base) (.object current)
  | current, (responseName, incoming)::rest =>
      ResponseAbsorbs (.object base)
        (.object (mergeResponseField responseName incoming current)) ∧
      MergeResponseFieldsAbsorbsFrom base
        (mergeResponseField responseName incoming current) rest

def ExecutableFieldsMergeCompatible (fields : List ExecutableField) : Prop :=
  ∀ first later,
    first ∈ fields ->
    later ∈ fields ->
    first.responseName = later.responseName ->
      first.parentType = later.parentType ∧
      first.fieldName = later.fieldName ∧
      first.arguments = later.arguments

def ExecutableFieldsValidationMergeCompatible
    (fields : List ExecutableField) : Prop :=
  ∀ first later,
    first ∈ fields ->
    later ∈ fields ->
    first.responseName = later.responseName ->
      first.parentType = later.parentType ∧
      first.fieldName = later.fieldName ∧
      Argument.argumentsEquivalent first.arguments later.arguments

def ExecutableFieldsSameParentValidationMergeCompatible
    (fields : List ExecutableField) : Prop :=
  ∀ first later,
    first ∈ fields ->
    later ∈ fields ->
    first.responseName = later.responseName ->
    first.parentType = later.parentType ->
      first.fieldName = later.fieldName ∧
      Argument.argumentsEquivalent first.arguments later.arguments

def ExecutableFieldsFieldValidationMergeCompatible
    (fields : List ExecutableField) : Prop :=
  ∀ first later,
    first ∈ fields ->
    later ∈ fields ->
    first.responseName = later.responseName ->
      first.fieldName = later.fieldName ∧
      Argument.argumentsEquivalent first.arguments later.arguments

def ExecutableFieldsArgumentsNodup
    (fields : List ExecutableField) : Prop :=
  ∀ field, field ∈ fields ->
    (field.arguments.map Argument.name).Nodup

def ExecutableFieldsSameResponseParent
    (fields : List ExecutableField) : Prop :=
  ∀ first later,
    first ∈ fields ->
    later ∈ fields ->
    first.responseName = later.responseName ->
      first.parentType = later.parentType

def ExecutableFieldsParent
    (parentType : Name) (fields : List ExecutableField) : Prop :=
  ∀ field, field ∈ fields -> field.parentType = parentType

def ScopedFieldsValidationMergeCompatible
    (fields : List FieldMerge.ScopedField) : Prop :=
  ∀ first later,
    first ∈ fields ->
    later ∈ fields ->
    first.responseName = later.responseName ->
    first.parentType = later.parentType ->
      first.fieldName = later.fieldName ∧
      Argument.argumentsEquivalent first.arguments later.arguments

def ScopedFieldsSameResponseParent
    (fields : List FieldMerge.ScopedField) : Prop :=
  ∀ first later,
    first ∈ fields ->
    later ∈ fields ->
    first.responseName = later.responseName ->
      first.parentType = later.parentType

def ScopedFieldsFieldValidationMergeCompatible
    (fields : List FieldMerge.ScopedField) : Prop :=
  ∀ first later,
    first ∈ fields ->
    later ∈ fields ->
    first.responseName = later.responseName ->
      first.fieldName = later.fieldName ∧
      Argument.argumentsEquivalent first.arguments later.arguments

-- Proof-facing strengthening of GraphQL field merge compatibility for the scoped
-- query fragment currently under consideration: every duplicated response key is
-- the same semantic field with equivalent arguments.
def ScopedFieldsNoAliasCollision
    (fields : List FieldMerge.ScopedField) : Prop :=
  ScopedFieldsFieldValidationMergeCompatible fields

def OperationNoAliasCollision (schema : Schema) (operation : Operation) : Prop :=
  ScopedFieldsNoAliasCollision
    (FieldMerge.collectFields schema operation.rootType operation.selectionSet)

def ScopedFieldRuntimeApplies
    (schema : Schema) (runtimeType : Name)
    (field : FieldMerge.ScopedField) : Prop :=
  schema.typeIncludesObjectBool field.parentType runtimeType = true

def ScopedParentRuntimeApplies
    (schema : Schema) (runtimeType parentType : Name) : Prop :=
  schema.typeIncludesObjectBool parentType runtimeType = true

theorem ScopedParentRuntimeApplies.of_rootSourceAppliesBool
    {ObjectIdentity : Type}
    (schema : Schema) (operation : Operation)
    (runtimeType : Name) (identity : ObjectIdentity) :
    rootSourceAppliesBool schema operation (.object runtimeType (some identity)) = true ->
      ScopedParentRuntimeApplies schema runtimeType operation.rootType := by
  intro hroot
  simpa [rootSourceAppliesBool, runtimeObjectType?] using hroot

theorem ScopedParentRuntimeApplies.of_typeIncludesObjectBool
    (schema : Schema) (runtimeType parentType : Name) :
    schema.typeIncludesObjectBool parentType runtimeType = true ->
      ScopedParentRuntimeApplies schema runtimeType parentType := by
  intro hincludes
  exact hincludes

theorem ScopedParentRuntimeApplies.runtimeObjectType
    (schema : Schema) {runtimeType parentType : Name} :
    SchemaWellFormedness.schemaWellFormed schema ->
    ScopedParentRuntimeApplies schema runtimeType parentType ->
      schema.objectType runtimeType := by
  intro hschema hparentRuntime
  exact SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
    parentType runtimeType (List.contains_iff_mem.mp hparentRuntime)

theorem ScopedParentRuntimeApplies.runtimeSelf
    (schema : Schema) {runtimeType parentType : Name} :
    SchemaWellFormedness.schemaWellFormed schema ->
    ScopedParentRuntimeApplies schema runtimeType parentType ->
      schema.typeIncludesObjectBool runtimeType runtimeType = true := by
  intro hschema hparentRuntime
  exact NormalForm.object_typeIncludesObjectBool_self schema
    (ScopedParentRuntimeApplies.runtimeObjectType schema hschema
      hparentRuntime)

theorem ScopedFieldsNoAliasCollision.fieldCompatible
    (fields : List FieldMerge.ScopedField) :
    ScopedFieldsNoAliasCollision fields ->
      ScopedFieldsFieldValidationMergeCompatible fields := by
  intro hnoAlias
  exact hnoAlias

theorem ScopedFieldsNoAliasCollision.prefix_selection
    (schema : Schema) (parentType : Name)
    (selectionSet prefixSelections suffix : List Selection)
    (selection : Selection) :
    ScopedFieldsNoAliasCollision
      (FieldMerge.collectFields schema parentType selectionSet) ->
    selectionSet = prefixSelections ++ selection :: suffix ->
      ScopedFieldsNoAliasCollision
        (FieldMerge.collectFields schema parentType [selection]) := by
  intro hnoAlias hselectionSet
  unfold ScopedFieldsNoAliasCollision
  change ScopedFieldsFieldValidationMergeCompatible
    (FieldMerge.collectFields schema parentType selectionSet) at hnoAlias
  unfold ScopedFieldsFieldValidationMergeCompatible at hnoAlias ⊢
  intro first later hfirst hlater hresponse
  apply hnoAlias first later
  · rw [hselectionSet]
    apply GraphQL.NormalForm.fieldMerge_collectFields_append_right_mem
      schema parentType prefixSelections (selection :: suffix)
    apply GraphQL.NormalForm.fieldMerge_collectFields_append_left_mem
      schema parentType [selection] suffix
    exact hfirst
  · rw [hselectionSet]
    apply GraphQL.NormalForm.fieldMerge_collectFields_append_right_mem
      schema parentType prefixSelections (selection :: suffix)
    apply GraphQL.NormalForm.fieldMerge_collectFields_append_left_mem
      schema parentType [selection] suffix
    exact hlater
  · exact hresponse

theorem OperationNoAliasCollision.prefix_selection
    (schema : Schema) (operation : Operation)
    (prefixSelections suffix : List Selection) (selection : Selection) :
    OperationNoAliasCollision schema operation ->
    operation.selectionSet = prefixSelections ++ selection :: suffix ->
      ScopedFieldsNoAliasCollision
        (FieldMerge.collectFields schema operation.rootType [selection]) := by
  intro hnoAlias hselectionSet
  exact ScopedFieldsNoAliasCollision.prefix_selection schema operation.rootType
    operation.selectionSet prefixSelections suffix selection hnoAlias
    hselectionSet

structure ValidOperationPrefixSelectionState
    (schema : Schema) (operation : Operation)
    (prefixSelections : List Selection) (selection : Selection)
    (suffix : List Selection) : Prop where
  selectionValid :
    Validation.selectionValid schema operation.variableDefinitions
      operation.rootType selection
  fieldsInSetCanMerge :
    FieldMerge.fieldsInSetCanMerge schema operation.rootType [selection]
  noAlias :
    ScopedFieldsNoAliasCollision
      (FieldMerge.collectFields schema operation.rootType [selection])

theorem ValidOperationPrefixSelectionState.of_valid_noAlias
    (schema : Schema) (operation : Operation)
    (prefixSelections suffix : List Selection) (selection : Selection)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hnoAlias : OperationNoAliasCollision schema operation)
    (hselectionSet :
      operation.selectionSet = prefixSelections ++ selection :: suffix) :
    ValidOperationPrefixSelectionState schema operation prefixSelections
      selection suffix := by
  exact
    { selectionValid :=
        by
          have hselSet : Validation.selectionSetValid schema operation.variableDefinitions operation.rootType (prefixSelections ++ selection :: suffix) := by
            rw [← hselectionSet]
            exact Validation.operationDefinitionValid_selectionSetValid hvalid
          have hright : Validation.selectionSetValid schema operation.variableDefinitions operation.rootType (selection :: suffix) :=
            Validation.selectionSetValid_append_right hselSet
          exact (by
            simp [Validation.selectionSetValid] at hright
            exact hright.1)
      fieldsInSetCanMerge :=
        by
          have hmergeAll : FieldMerge.fieldsInSetCanMerge schema operation.rootType (prefixSelections ++ selection :: suffix) := by
            rw [← hselectionSet]
            exact Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
          have hright : FieldMerge.fieldsInSetCanMerge schema operation.rootType (selection :: suffix) :=
            GraphQL.NormalForm.fieldsInSetCanMerge_append_right schema operation.rootType prefixSelections (selection :: suffix) hmergeAll
          exact GraphQL.NormalForm.fieldsInSetCanMerge_append_left schema operation.rootType [selection] suffix hright
      noAlias :=
        OperationNoAliasCollision.prefix_selection schema operation
          prefixSelections suffix selection hnoAlias hselectionSet }

theorem ValidOperationPrefixSelectionState.field_lookup
    {schema : Schema} {operation : Operation}
    {prefixSelections suffix : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {selectionSet : List Selection} :
    ValidOperationPrefixSelectionState schema operation prefixSelections
      (.field responseName fieldName arguments directives selectionSet)
      suffix ->
      ∃ fieldDefinition,
        schema.lookupField operation.rootType fieldName = some fieldDefinition
          ∧ Validation.argumentsValid schema fieldDefinition.arguments
            operation.variableDefinitions arguments
          ∧ Validation.fieldSelectionSetValid schema
            operation.variableDefinitions fieldDefinition selectionSet := by
  intro hstate
  exact Validation.selectionValid_field_lookup hstate.selectionValid

theorem ValidOperationPrefixSelectionState.inline_none_selectionSetValid
    {schema : Schema} {operation : Operation}
    {prefixSelections suffix : List Selection}
    {directives : List DirectiveApplication} {selectionSet : List Selection} :
    ValidOperationPrefixSelectionState schema operation prefixSelections
      (.inlineFragment none directives selectionSet) suffix ->
      Validation.selectionSetValid schema operation.variableDefinitions
        operation.rootType selectionSet := by
  intro hstate
  exact
    Validation.selectionValid_inlineFragment_none_selectionSetValid
      hstate.selectionValid

theorem ValidOperationPrefixSelectionState.inline_some_selectionSetValid
    {schema : Schema} {operation : Operation}
    {prefixSelections suffix : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    {selectionSet : List Selection} :
    ValidOperationPrefixSelectionState schema operation prefixSelections
      (.inlineFragment (some typeCondition) directives selectionSet) suffix ->
      Validation.selectionSetValid schema operation.variableDefinitions
        typeCondition selectionSet := by
  intro hstate
  exact
    Validation.selectionValid_inlineFragment_some_selectionSetValid
      hstate.selectionValid

theorem ScopedFieldRuntimeApplies.mergeIdentityCondition
    (schema : Schema) (runtimeType : Name)
    (first later : FieldMerge.ScopedField) :
    ScopedFieldRuntimeApplies schema runtimeType first ->
    ScopedFieldRuntimeApplies schema runtimeType later ->
      first.parentType = later.parentType
        ∨ ¬ schema.objectType first.parentType
        ∨ ¬ schema.objectType later.parentType := by
  intro hfirst hlater
  by_cases hfirstObject : schema.objectType first.parentType
  · by_cases hlaterObject : schema.objectType later.parentType
    · have hfirstRuntime :
          runtimeType = first.parentType :=
        object_typeIncludesObjectBool_eq_self schema hfirstObject
          hfirst
      have hlaterRuntime :
          runtimeType = later.parentType :=
        object_typeIncludesObjectBool_eq_self schema hlaterObject
          hlater
      exact Or.inl (hfirstRuntime.symm.trans hlaterRuntime)
    · exact Or.inr (Or.inr hlaterObject)
  · exact Or.inr (Or.inl hfirstObject)

def ScopedFieldMatchesExecutable
    (scopedField : FieldMerge.ScopedField)
    (executableField : ExecutableField) : Prop :=
  scopedField.parentType = executableField.parentType
    ∧ scopedField.responseName = executableField.responseName
    ∧ scopedField.fieldName = executableField.fieldName
    ∧ scopedField.arguments = executableField.arguments
    ∧ scopedField.selectionSet = executableField.selectionSet

def ScopedFieldMatchesExecutableIdentity
    (scopedField : FieldMerge.ScopedField)
    (executableField : ExecutableField) : Prop :=
  scopedField.responseName = executableField.responseName
    ∧ scopedField.fieldName = executableField.fieldName
    ∧ scopedField.arguments = executableField.arguments
    ∧ scopedField.selectionSet = executableField.selectionSet

def ExecutableFieldsScopedBy
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField) : Prop :=
  ∀ field, field ∈ fields ->
    ∃ scopedField,
      scopedField ∈ scopedFields ∧
      ScopedFieldMatchesExecutable scopedField field

def ExecutableFieldsIdentityScopedBy
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField) : Prop :=
  ∀ field, field ∈ fields ->
    ∃ scopedField,
      scopedField ∈ scopedFields ∧
      ScopedFieldMatchesExecutableIdentity scopedField field

def ExecutableFieldsRuntimeScopedBy
    (schema : Schema) (runtimeType : Name)
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField) : Prop :=
  ∀ field, field ∈ fields ->
    ∃ scopedField,
      scopedField ∈ scopedFields
        ∧ ScopedFieldMatchesExecutableIdentity scopedField field
        ∧ ScopedFieldRuntimeApplies schema runtimeType scopedField

theorem ScopedFieldMatchesExecutable.identity
    {scopedField : FieldMerge.ScopedField}
    {executableField : ExecutableField} :
    ScopedFieldMatchesExecutable scopedField executableField ->
      ScopedFieldMatchesExecutableIdentity scopedField executableField := by
  intro hmatch
  rcases hmatch with
    ⟨_hparent, hresponseName, hfieldName, harguments, hselectionSet⟩
  exact ⟨hresponseName, hfieldName, harguments, hselectionSet⟩

theorem ExecutableFieldsScopedBy.identity
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField) :
    ExecutableFieldsScopedBy scopedFields fields ->
      ExecutableFieldsIdentityScopedBy scopedFields fields := by
  intro hscoped field hfield
  rcases hscoped field hfield with
    ⟨scopedField, hscopedMem, hmatch⟩
  exact
    ⟨scopedField, hscopedMem, ScopedFieldMatchesExecutable.identity hmatch⟩

theorem ExecutableFieldsRuntimeScopedBy.identityScopedBy
    (schema : Schema) (runtimeType : Name)
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField) :
    ExecutableFieldsRuntimeScopedBy schema runtimeType scopedFields fields ->
      ExecutableFieldsIdentityScopedBy scopedFields fields := by
  intro hscoped field hfield
  rcases hscoped field hfield with
    ⟨scopedField, hscopedMem, hmatch, _hruntime⟩
  exact ⟨scopedField, hscopedMem, hmatch⟩

theorem ExecutableFieldsRuntimeScopedBy.mono
    (schema : Schema) (runtimeType : Name)
    (scopedFields : List FieldMerge.ScopedField)
    (source target : List ExecutableField) :
    (∀ field, field ∈ target -> field ∈ source) ->
    ExecutableFieldsRuntimeScopedBy schema runtimeType scopedFields source ->
      ExecutableFieldsRuntimeScopedBy schema runtimeType scopedFields target := by
  intro hsubset hscoped field hfield
  exact hscoped field (hsubset field hfield)

def ExecutableFieldsResolveStable
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : Value ObjectIdentity) (fields : List ExecutableField) : Prop :=
  ∀ first later,
    first ∈ fields ->
    later ∈ fields ->
    first.responseName = later.responseName ->
      resolvers.resolve first.parentType first.fieldName first.arguments source =
      resolvers.resolve later.parentType later.fieldName later.arguments source

def ResolversRespectArgumentEquivalence
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : Value ObjectIdentity) : Prop :=
  ∀ parentType fieldName firstArguments laterArguments,
    Argument.argumentsEquivalent firstArguments laterArguments ->
      resolvers.resolve parentType fieldName firstArguments source =
      resolvers.resolve parentType fieldName laterArguments source

def ResolversRespectFieldAndArgumentEquivalence
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : Value ObjectIdentity) : Prop :=
  ∀ firstParent laterParent fieldName firstArguments laterArguments,
    Argument.argumentsEquivalent firstArguments laterArguments ->
      resolvers.resolve firstParent fieldName firstArguments source =
      resolvers.resolve laterParent fieldName laterArguments source

def ResolversRespectValidFieldAndArgumentEquivalence
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : Value ObjectIdentity) : Prop :=
  ∀ firstParent laterParent fieldName firstArguments laterArguments,
    (firstArguments.map Argument.name).Nodup ->
      (laterArguments.map Argument.name).Nodup ->
        Argument.argumentsEquivalent firstArguments laterArguments ->
          resolvers.resolve firstParent fieldName firstArguments source =
          resolvers.resolve laterParent fieldName laterArguments source

theorem ExecutableFieldsResolveStable.tail
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : Value ObjectIdentity) (field : ExecutableField)
    (fields : List ExecutableField) :
    ExecutableFieldsResolveStable resolvers source (field :: fields) ->
      ExecutableFieldsResolveStable resolvers source fields := by
  intro hstable first later hfirst hlater hresponse
  exact hstable first later (by simp [hfirst]) (by simp [hlater]) hresponse

theorem ExecutableFieldsResolveStable.head_eq_later
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : Value ObjectIdentity) (field later : ExecutableField)
    (fields : List ExecutableField) :
    ExecutableFieldsResolveStable resolvers source (field :: fields) ->
    later ∈ fields ->
    field.responseName = later.responseName ->
      resolvers.resolve field.parentType field.fieldName field.arguments
        source =
      resolvers.resolve later.parentType later.fieldName later.arguments
        source := by
  intro hstable hlater hresponse
  exact hstable field later (by simp) (by simp [hlater]) hresponse

structure ExecutedResponseFieldAt
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (source : Value ObjectIdentity) (output : Response)
    (field : ExecutableField) (response : Response) where
  previous : Response
  resolved : Value ObjectIdentity
  previous_eq :
    previous = (responseObjectField? field.responseName output).getD .null
  resolved_eq :
    resolved =
      resolvers.resolve field.parentType field.fieldName field.arguments source
  response_eq :
    response =
      completeValue schema resolvers variableValues completionDepth
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        field.selectionSet resolved previous

def executableFieldSelection (field : ExecutableField) : Selection :=
  .field field.responseName field.fieldName field.arguments [] field.selectionSet

def executableFieldSelections (fields : List ExecutableField) :
    List Selection :=
  fields.map executableFieldSelection

theorem selectionDirectivesAllowBool_empty
    (variableValues : VariableValues) :
    selectionDirectivesAllowBool variableValues [] = true := by
  rfl

theorem collectSelection_executableFieldSelection
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (field : ExecutableField) :
    GraphQL.Execution.collectSelection schema variableValues parentType source
      (executableFieldSelection field) =
    [(field.responseName, [{ field with parentType := parentType }])] := by
  simp [executableFieldSelection, GraphQL.Execution.collectSelection,
    selectionDirectivesAllowBool_empty]

theorem collectSelection_executableFieldSelection_of_parent
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (field : ExecutableField) :
    field.parentType = parentType ->
      GraphQL.Execution.collectSelection schema variableValues parentType source
        (executableFieldSelection field) =
      [(field.responseName, [field])] := by
  intro hparent
  cases field with
  | mk fieldParent responseName fieldName arguments selectionSet =>
      dsimp at hparent ⊢
      subst fieldParent
      simp [collectSelection_executableFieldSelection]

theorem collectFields_executableFieldSelections_same_group
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) :
    ∀ fields : List ExecutableField,
      (∀ field, field ∈ fields -> field.responseName = responseName) ->
      (∀ field, field ∈ fields -> field.parentType = parentType) ->
        GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections fields) =
        match fields with
        | [] => []
        | _field :: _rest => [(responseName, fields)]
  | [], _hresponse, _hparent => by
      simp [executableFieldSelections, GraphQL.Execution.collectFields]
  | field :: rest, hresponse, hparent => by
      have hfieldResponse : field.responseName = responseName :=
        hresponse field (by simp)
      have hfieldParent : field.parentType = parentType :=
        hparent field (by simp)
      have hrestResponse :
          ∀ restField, restField ∈ rest ->
            restField.responseName = responseName := by
        intro restField hmem
        exact hresponse restField (by simp [hmem])
      have hrestParent :
          ∀ restField, restField ∈ rest ->
            restField.parentType = parentType := by
        intro restField hmem
        exact hparent restField (by simp [hmem])
      cases rest with
      | nil =>
          simp [executableFieldSelections, GraphQL.Execution.collectFields,
            collectSelection_executableFieldSelection_of_parent schema
              variableValues parentType source field hfieldParent,
            GraphQL.Execution.mergeExecutableGroups, hfieldResponse]
      | cons next restTail =>
          have hrestCollect :=
            collectFields_executableFieldSelections_same_group schema
              variableValues parentType source responseName (next :: restTail)
              hrestResponse hrestParent
          change
            GraphQL.Execution.mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                parentType source (executableFieldSelection field))
              (GraphQL.Execution.collectFields schema variableValues parentType
                source (executableFieldSelections (next :: restTail))) =
            [(responseName, field :: next :: restTail)]
          rw [collectSelection_executableFieldSelection_of_parent schema
            variableValues parentType source field hfieldParent, hrestCollect]
          simp [GraphQL.Execution.mergeExecutableGroups,
            GraphQL.Execution.addExecutableGroup, hfieldResponse]

theorem specExecuteRootSelectionSet_executableFieldSelections_same_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = parentType) :
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source (executableFieldSelections (field :: fields)) =
    GraphQL.Execution.executeCollectedFields schema resolvers variableValues
      depth source [(responseName, field :: fields)] := by
  simp [GraphQL.Execution.executeRootSelectionSet,
    collectFields_executableFieldSelections_same_group schema variableValues
      parentType source responseName (field :: fields) hresponse hparent]

theorem ResolversRespectFieldAndArgumentEquivalence.to_valid
    {ObjectIdentity : Type} {resolvers : Resolvers ObjectIdentity}
    {source : Value ObjectIdentity} :
    ResolversRespectFieldAndArgumentEquivalence resolvers source ->
      ResolversRespectValidFieldAndArgumentEquivalence resolvers source := by
  intro hrespect firstParent laterParent fieldName firstArguments
    laterArguments _hfirstNodup _hlaterNodup hequivalent
  exact hrespect firstParent laterParent fieldName firstArguments
    laterArguments hequivalent

def CollectedGroupsMergeCompatible
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField)) : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups ->
      ExecutableFieldsMergeCompatible fields ∧
      ExecutableFieldsResolveStable resolvers source fields

def CollectedGroupsSameResponseParent
    (groups : List (Name × List ExecutableField)) : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups ->
      ExecutableFieldsSameResponseParent fields

def CollectedGroupsParent
    (parentType : Name)
    (groups : List (Name × List ExecutableField)) : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups ->
      ExecutableFieldsParent parentType fields

def ExecutableFieldsResponseName
    (responseName : Name) (fields : List ExecutableField) : Prop :=
  ∀ field, field ∈ fields -> field.responseName = responseName

def CollectedGroupsResponseName
    (groups : List (Name × List ExecutableField)) : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups ->
      ExecutableFieldsResponseName responseName fields

def CollectedGroupsFieldsNonempty
    (groups : List (Name × List ExecutableField)) : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups ->
      fields ≠ []

theorem CollectedGroupsFieldsNonempty_nil :
    CollectedGroupsFieldsNonempty [] := by
  intro _responseName _fields hmem
  simp at hmem

theorem CollectedGroupsFieldsNonempty_singleton
    (responseName : Name) (fields : List ExecutableField) :
    fields ≠ [] ->
      CollectedGroupsFieldsNonempty [(responseName, fields)] := by
  intro hfields groupResponseName groupFields hmem
  have hgroup :
      (groupResponseName, groupFields) = (responseName, fields) := by
    simpa using hmem
  cases hgroup
  exact hfields

theorem CollectedGroupsFieldsNonempty_tail
    {group : Name × List ExecutableField}
    {groups : List (Name × List ExecutableField)} :
    CollectedGroupsFieldsNonempty (group :: groups) ->
      CollectedGroupsFieldsNonempty groups := by
  intro hgroups responseName fields hmem
  exact hgroups responseName fields (by simp [hmem])

theorem CollectedGroupsFieldsNonempty_addExecutableGroup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField)) :
    group.snd ≠ [] ->
      CollectedGroupsFieldsNonempty groups ->
        CollectedGroupsFieldsNonempty
          (GraphQL.Execution.addExecutableGroup group groups) := by
  rcases group with ⟨groupName, groupFields⟩
  intro hgroup hgroups
  induction groups with
  | nil =>
      simpa [GraphQL.Execution.addExecutableGroup] using
        CollectedGroupsFieldsNonempty_singleton groupName groupFields hgroup
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · have hcurrentNonempty : currentFields ≠ [] :=
          hgroups currentName currentFields (by simp)
        have happendNonempty : currentFields ++ groupFields ≠ [] := by
          cases currentFields with
          | nil => exact False.elim (hcurrentNonempty rfl)
          | cons _ _ => simp
        intro responseName fields hmem
        simp [GraphQL.Execution.addExecutableGroup, hname] at hmem
        rcases hmem with hhead | htail
        · have hfields :
              fields = currentFields ++ groupFields := by
            simpa using hhead.2
          subst fields
          exact happendNonempty
        · exact hgroups responseName fields (by simp [htail])
      · have hfalse : (currentName == groupName) = false := by
          cases hmatch : currentName == groupName
          · rfl
          · contradiction
        intro responseName fields hmem
        simp [GraphQL.Execution.addExecutableGroup, hfalse] at hmem
        rcases hmem with hhead | htail
        · have hfields : fields = currentFields := by
            simpa using hhead.2
          subst fields
          exact hgroups currentName currentFields (by simp)
        · exact ih (CollectedGroupsFieldsNonempty_tail hgroups)
            responseName fields htail

theorem CollectedGroupsFieldsNonempty_mergeExecutableGroups
    (left right : List (Name × List ExecutableField)) :
    CollectedGroupsFieldsNonempty left ->
      CollectedGroupsFieldsNonempty right ->
        CollectedGroupsFieldsNonempty
          (GraphQL.Execution.mergeExecutableGroups left right) := by
  intro hleft hright
  induction right generalizing left with
  | nil =>
      simpa [GraphQL.Execution.mergeExecutableGroups] using hleft
  | cons group rest ih =>
      exact ih (GraphQL.Execution.addExecutableGroup group left)
        (CollectedGroupsFieldsNonempty_addExecutableGroup group left
          (hright group.fst group.snd (by simp)) hleft)
        (CollectedGroupsFieldsNonempty_tail hright)

theorem ExecutableFieldsParent.sameResponseParent
    (parentType : Name) (fields : List ExecutableField) :
    ExecutableFieldsParent parentType fields ->
      ExecutableFieldsSameResponseParent fields := by
  intro hparent first later hfirst hlater _hresponse
  rw [hparent first hfirst, hparent later hlater]

theorem CollectedGroupsParent.sameResponseParent
    (parentType : Name) (groups : List (Name × List ExecutableField)) :
    CollectedGroupsParent parentType groups ->
      CollectedGroupsSameResponseParent groups := by
  intro hparent responseName fields hmem
  exact ExecutableFieldsParent.sameResponseParent parentType fields
    (hparent responseName fields hmem)

theorem ExecutableFieldsResponseName_singleton
    (responseName : Name) (field : ExecutableField) :
    field.responseName = responseName ->
      ExecutableFieldsResponseName responseName [field] := by
  intro hfield candidate hmem
  have hcandidate : candidate = field := by
    simpa using hmem
  subst candidate
  exact hfield

theorem ExecutableFieldsResponseName_append
    (responseName : Name) (left right : List ExecutableField) :
    ExecutableFieldsResponseName responseName left ->
      ExecutableFieldsResponseName responseName right ->
        ExecutableFieldsResponseName responseName (left ++ right) := by
  intro hleft hright field hmem
  rcases List.mem_append.mp hmem with hfield | hfield
  · exact hleft field hfield
  · exact hright field hfield

theorem CollectedGroupsResponseName_nil :
    CollectedGroupsResponseName [] := by
  intro _responseName _fields hmem
  simp at hmem

theorem CollectedGroupsResponseName_singleton
    (responseName : Name) (fields : List ExecutableField) :
    ExecutableFieldsResponseName responseName fields ->
      CollectedGroupsResponseName [(responseName, fields)] := by
  intro hfields groupResponseName groupFields hmem
  have hpair :
      (groupResponseName, groupFields) = (responseName, fields) := by
    simpa using hmem
  cases hpair
  exact hfields

theorem CollectedGroupsResponseName_tail
    {group : Name × List ExecutableField}
    {groups : List (Name × List ExecutableField)} :
    CollectedGroupsResponseName (group :: groups) ->
      CollectedGroupsResponseName groups := by
  intro hgroups responseName fields hmem
  exact hgroups responseName fields (by simp [hmem])

theorem CollectedGroupsResponseName_addExecutableGroup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField)) :
    ExecutableFieldsResponseName group.fst group.snd ->
      CollectedGroupsResponseName groups ->
        CollectedGroupsResponseName
          (GraphQL.Execution.addExecutableGroup group groups) := by
  rcases group with ⟨groupName, groupFields⟩
  intro hgroup hgroups
  induction groups with
  | nil =>
      intro responseName fields hmem
      simp [GraphQL.Execution.addExecutableGroup] at hmem
      rcases hmem with ⟨hresponseName, hfields⟩
      cases hresponseName
      cases hfields
      exact hgroup
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · have hcurrent : currentName = groupName := beq_iff_eq.mp hname
        intro responseName fields hmem
        simp [GraphQL.Execution.addExecutableGroup, hname] at hmem
        rcases hmem with hhead | htail
        · rcases hhead with ⟨hresponseName, hfields⟩
          cases hresponseName
          cases hfields
          exact ExecutableFieldsResponseName_append currentName currentFields
            groupFields
            (hgroups currentName currentFields (by simp))
            (by simpa [hcurrent] using hgroup)
        · exact hgroups responseName fields (by simp [htail])
      · have hfalse : (currentName == groupName) = false := by
          cases hmatch : currentName == groupName
          · rfl
          · contradiction
        intro responseName fields hmem
        simp [GraphQL.Execution.addExecutableGroup, hfalse] at hmem
        rcases hmem with hhead | htail
        · rcases hhead with ⟨hresponseName, hfields⟩
          cases hresponseName
          cases hfields
          exact hgroups currentName currentFields (by simp)
        · exact ih (CollectedGroupsResponseName_tail hgroups)
            responseName fields htail

theorem CollectedGroupsResponseName_mergeExecutableGroups
    (left right : List (Name × List ExecutableField)) :
    CollectedGroupsResponseName left ->
      CollectedGroupsResponseName right ->
        CollectedGroupsResponseName
          (GraphQL.Execution.mergeExecutableGroups left right) := by
  intro hleft hright
  induction right generalizing left with
  | nil =>
      simpa [GraphQL.Execution.mergeExecutableGroups] using hleft
  | cons group rest ih =>
      simp [GraphQL.Execution.mergeExecutableGroups]
      exact ih (GraphQL.Execution.addExecutableGroup group left)
        (CollectedGroupsResponseName_addExecutableGroup group left
          (hright group.fst group.snd (by simp)) hleft)
        (CollectedGroupsResponseName_tail hright)

theorem ExecutableFieldsParent_singleton
    (parentType : Name) (field : ExecutableField) :
    field.parentType = parentType ->
      ExecutableFieldsParent parentType [field] := by
  intro hfield candidate hmem
  have hcandidate : candidate = field := by
    simpa using hmem
  subst candidate
  exact hfield

theorem ExecutableFieldsParent_append
    (parentType : Name) (left right : List ExecutableField) :
    ExecutableFieldsParent parentType left ->
      ExecutableFieldsParent parentType right ->
        ExecutableFieldsParent parentType (left ++ right) := by
  intro hleft hright field hmem
  rcases List.mem_append.mp hmem with hfield | hfield
  · exact hleft field hfield
  · exact hright field hfield

theorem CollectedGroupsParent_nil
    (parentType : Name) :
    CollectedGroupsParent parentType [] := by
  intro _responseName _fields hmem
  simp at hmem

theorem CollectedGroupsParent_singleton
    (parentType responseName : Name) (fields : List ExecutableField) :
    ExecutableFieldsParent parentType fields ->
      CollectedGroupsParent parentType [(responseName, fields)] := by
  intro hfields groupResponseName groupFields hmem
  have hpair :
      (groupResponseName, groupFields) = (responseName, fields) := by
    simpa using hmem
  cases hpair
  exact hfields

theorem CollectedGroupsParent_tail
    {parentType : Name}
    {group : Name × List ExecutableField}
    {groups : List (Name × List ExecutableField)} :
    CollectedGroupsParent parentType (group :: groups) ->
      CollectedGroupsParent parentType groups := by
  intro hgroups responseName fields hmem
  exact hgroups responseName fields (by simp [hmem])

theorem CollectedGroupsParent_addExecutableGroup
    (parentType : Name)
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField)) :
    ExecutableFieldsParent parentType group.snd ->
      CollectedGroupsParent parentType groups ->
        CollectedGroupsParent parentType
          (GraphQL.Execution.addExecutableGroup group groups) := by
  rcases group with ⟨groupName, groupFields⟩
  intro hgroup hgroups
  induction groups with
  | nil =>
      intro responseName fields hmem
      simp [GraphQL.Execution.addExecutableGroup] at hmem
      rcases hmem with ⟨_hresponseName, hfields⟩
      cases hfields
      exact hgroup
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · intro responseName fields hmem
        simp [GraphQL.Execution.addExecutableGroup, hname] at hmem
        rcases hmem with hhead | htail
        · rcases hhead with ⟨_hresponseName, hfields⟩
          cases hfields
          exact ExecutableFieldsParent_append parentType currentFields
            groupFields
            (hgroups currentName currentFields (by simp))
            hgroup
        · exact hgroups responseName fields (by simp [htail])
      · have hfalse : (currentName == groupName) = false := by
          cases hmatch : currentName == groupName
          · rfl
          · contradiction
        intro responseName fields hmem
        simp [GraphQL.Execution.addExecutableGroup, hfalse] at hmem
        rcases hmem with hhead | htail
        · rcases hhead with ⟨_hresponseName, hfields⟩
          cases hfields
          exact hgroups currentName currentFields (by simp)
        · exact ih (CollectedGroupsParent_tail hgroups)
            responseName fields htail

theorem CollectedGroupsParent_mergeExecutableGroups
    (parentType : Name)
    (left right : List (Name × List ExecutableField)) :
    CollectedGroupsParent parentType left ->
      CollectedGroupsParent parentType right ->
        CollectedGroupsParent parentType
          (GraphQL.Execution.mergeExecutableGroups left right) := by
  intro hleft hright
  induction right generalizing left with
  | nil =>
      simpa [GraphQL.Execution.mergeExecutableGroups] using hleft
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      simp [GraphQL.Execution.mergeExecutableGroups]
      exact ih (GraphQL.Execution.addExecutableGroup (responseName, fields) left)
        (CollectedGroupsParent_addExecutableGroup parentType
          (responseName, fields) left (hright responseName fields (by simp))
          hleft)
        (CollectedGroupsParent_tail hright)

mutual
  theorem collectSelection_parent
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : Value ObjectIdentity)
      (selection : Selection) :
      CollectedGroupsParent parentType
        (GraphQL.Execution.collectSelection schema variableValues parentType
          source selection) := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, hallows]
          exact CollectedGroupsParent_singleton parentType responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := selectionSet
            }]
            (ExecutableFieldsParent_singleton parentType
              {
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              } rfl)
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, hfalse,
            CollectedGroupsParent_nil]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · simp [GraphQL.Execution.collectSelection, hallows]
              exact collectFields_parent schema variableValues parentType source
                selectionSet
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsParent_nil]
        | some typeCondition =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition = true
              · simp [GraphQL.Execution.collectSelection, hallows, happly]
                exact collectFields_parent schema variableValues parentType
                  source selectionSet
              · have hfalse :
                    doesFragmentTypeApplyBool schema parentType source
                      typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema parentType source
                        typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, hallows, hfalse,
                  CollectedGroupsParent_nil]
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsParent_nil]

  theorem collectFields_parent
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : Value ObjectIdentity)
      (selectionSet : List Selection) :
      CollectedGroupsParent parentType
        (GraphQL.Execution.collectFields schema variableValues parentType
          source selectionSet) := by
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, CollectedGroupsParent_nil]
    | cons selection rest =>
        simp [GraphQL.Execution.collectFields]
        exact CollectedGroupsParent_mergeExecutableGroups parentType
          (GraphQL.Execution.collectSelection schema variableValues parentType
            source selection)
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (collectSelection_parent schema variableValues parentType source
            selection)
          (collectFields_parent schema variableValues parentType source rest)
end

mutual
  theorem collectSelection_responseName
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : Value ObjectIdentity)
      (selection : Selection) :
      CollectedGroupsResponseName
        (GraphQL.Execution.collectSelection schema variableValues parentType
          source selection) := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, hallows]
          exact CollectedGroupsResponseName_singleton responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := selectionSet
            }]
            (ExecutableFieldsResponseName_singleton responseName
              {
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              } rfl)
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, hfalse,
            CollectedGroupsResponseName_nil]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · simp [GraphQL.Execution.collectSelection, hallows]
              exact collectFields_responseName schema variableValues parentType
                source selectionSet
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsResponseName_nil]
        | some typeCondition =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition = true
              · simp [GraphQL.Execution.collectSelection, hallows, happly]
                exact collectFields_responseName schema variableValues
                  parentType source selectionSet
              · have hfalse :
                    doesFragmentTypeApplyBool schema parentType source
                      typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema parentType source
                        typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, hallows, hfalse,
                  CollectedGroupsResponseName_nil]
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsResponseName_nil]

  theorem collectFields_responseName
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : Value ObjectIdentity)
      (selectionSet : List Selection) :
      CollectedGroupsResponseName
        (GraphQL.Execution.collectFields schema variableValues parentType
          source selectionSet) := by
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, CollectedGroupsResponseName_nil]
    | cons selection rest =>
        simp [GraphQL.Execution.collectFields]
        exact CollectedGroupsResponseName_mergeExecutableGroups
          (GraphQL.Execution.collectSelection schema variableValues parentType
            source selection)
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (collectSelection_responseName schema variableValues parentType source
            selection)
          (collectFields_responseName schema variableValues parentType source
            rest)
end

mutual
  theorem collectSelection_fieldsNonempty
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : Value ObjectIdentity)
      (selection : Selection) :
      CollectedGroupsFieldsNonempty
        (GraphQL.Execution.collectSelection schema variableValues parentType
          source selection) := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, hallows]
          exact CollectedGroupsFieldsNonempty_singleton responseName
            [{ parentType := parentType
               responseName := responseName
               fieldName := fieldName
               arguments := arguments
               selectionSet := selectionSet }]
            (by simp)
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, hfalse,
            CollectedGroupsFieldsNonempty_nil]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · simp [GraphQL.Execution.collectSelection, hallows]
              exact collectFields_fieldsNonempty schema variableValues
                parentType source selectionSet
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsFieldsNonempty_nil]
        | some typeCondition =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition = true
              · simp [GraphQL.Execution.collectSelection, hallows, happly]
                exact collectFields_fieldsNonempty schema variableValues
                  parentType source selectionSet
              · have hfalse :
                    doesFragmentTypeApplyBool schema parentType source
                      typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema parentType source
                        typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, hallows, hfalse,
                  CollectedGroupsFieldsNonempty_nil]
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsFieldsNonempty_nil]

  theorem collectFields_fieldsNonempty
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : Value ObjectIdentity)
      (selectionSet : List Selection) :
      CollectedGroupsFieldsNonempty
        (GraphQL.Execution.collectFields schema variableValues parentType
          source selectionSet) := by
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields,
          CollectedGroupsFieldsNonempty_nil]
    | cons selection rest =>
        simp [GraphQL.Execution.collectFields]
        exact CollectedGroupsFieldsNonempty_mergeExecutableGroups
          (GraphQL.Execution.collectSelection schema variableValues parentType
            source selection)
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (collectSelection_fieldsNonempty schema variableValues parentType
            source selection)
          (collectFields_fieldsNonempty schema variableValues parentType source
            rest)
end

theorem collectFields_sameResponseParent
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) :
    CollectedGroupsSameResponseParent
      (GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet) :=
  CollectedGroupsParent.sameResponseParent parentType
    (GraphQL.Execution.collectFields schema variableValues parentType source
      selectionSet)
    (collectFields_parent schema variableValues parentType source selectionSet)

def CollectedGroupsValidationMergeCompatible
    (groups : List (Name × List ExecutableField)) : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups ->
      ExecutableFieldsSameParentValidationMergeCompatible fields

def CollectedGroupsFieldValidationMergeCompatible
    (groups : List (Name × List ExecutableField)) : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups ->
      ExecutableFieldsFieldValidationMergeCompatible fields

end ExecutionUngrouped
end Algorithms

end GraphQL
