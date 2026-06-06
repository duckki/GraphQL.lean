import GraphQL.Operation

/-!
Spec reference: GraphQL September 2025.
- 6.1-6.2 Executing Requests and Operations: this module executes the modeled single
  query-like operation, not full request validation/coercion or mutation/subscription
  modes.
- 6.3 Executing Selection Sets: field collection, grouped field execution, and subfield
  merging are represented over selections.
- 6.4 Executing Fields: resolver invocation and value completion are approximated;
  argument coercion, result coercion, asynchronous behavior, and error propagation are
  omitted.
- 7 Response: response values model data only, without `errors`, `extensions`, or request
  error results.
-/
namespace GraphQL

namespace Execution

-- Spec 6.4.3 values before completion: non-spec internal value domain used to stand in
-- for host-language resolver results.
inductive Value where
  | null
  | scalar (value : String)
  | object (typeName : Name) (identity : Nat)
  | list (values : List Value)
deriving Repr

-- Spec 7.1.5 `data`: partial; models response data recursively, omitting request error
-- results, execution errors, extensions, response positions, and serialization details.
inductive Response where
  | null
  | scalar (value : String)
  | object (fields : List (Name × Response))
  | list (values : List Response)
deriving Repr

-- Spec 6.4.2 `ResolveFieldValue`: partial; one synchronous resolver function stands in
-- for object-type field resolvers and receives uncoerced modeled arguments.
structure Resolvers where
  resolve : Name -> Name -> List Argument -> Value -> Value

-- Spec 6.1.2 `CoerceVariableValues`: partial; variables are assumed already supplied as
-- modeled input values without coercion or validation.
abbrev VariableValues := List (Name × InputValue)

-- Spec 6.1.2 variable value lookup helper for already-coerced modeled variables.
def lookupVariableValue? (variableValues : VariableValues) (name : Name) : Option InputValue :=
  match variableValues with
  | [] => none
  | (variableName, value) :: rest =>
      if variableName = name then some value else lookupVariableValue? rest name

-- Spec 3.13.1 `@skip` / 3.13.2 `@include`: partial; resolves only Boolean literals or
-- variables bound to Boolean literals.
def inputValueBoolean? (variableValues : VariableValues) : InputValue -> Option Bool
  | .variable name => do
      let value <- lookupVariableValue? variableValues name
      value.staticBoolean?
  | value => value.staticBoolean?

-- Spec 6.3.2 `CollectFields` inline `@skip`/`@include` checks: local per-directive
-- helper, not a named spec algorithm.
def directiveAllowsSelectionBool (variableValues : VariableValues) : DirectiveApplication -> Bool
  | .skip ifArgument =>
      match inputValueBoolean? variableValues ifArgument with
      | some value => !value
      | none => false
  | .include ifArgument =>
      match inputValueBoolean? variableValues ifArgument with
      | some value => value
      | none => false

-- Spec 6.3.2 `CollectFields` inline directive checks: local helper over one selection's
-- directive list, not a named spec algorithm.
def selectionDirectivesAllowBool (variableValues : VariableValues)
    (directives : List DirectiveApplication) : Bool :=
  directives.all (fun directive => directiveAllowsSelectionBool variableValues directive)

-- Spec 6.4.3 `CompleteValue`: partial fallback for exhausted execution depth; converts
-- internal values structurally without type-directed coercion or errors.
def shallowResponse : Value -> Response
  | .null => .null
  | .scalar value => .scalar value
  | .object _typeName _identity => .object []
  | .list values => .list (values.map shallowResponse)

-- Spec 6.3.2 `DoesFragmentTypeApply` needs a runtime object type when the source value
-- is object-like.
def runtimeObjectType? : Value -> Option Name
  | .object typeName _identity => some typeName
  | _ => none

-- Spec 6.3.2 `DoesFragmentTypeApply`: partial; faithful when runtime object type is
-- known, but falls back to parent/type overlap for non-object placeholder values.
def doesFragmentTypeApplyBool (schema : Schema) (parentType : Name)
    (source : Value) (typeCondition : Name) : Bool :=
  match runtimeObjectType? source with
  | some objectName => schema.typeIncludesObjectBool typeCondition objectName
  | none => schema.typesOverlapBool parentType typeCondition

-- Spec 6.3.2 collected field entries: non-spec helper carrying the data needed to execute
-- one grouped response name.
structure ExecutableField where
  parentType : Name
  responseName : Name
  fieldName : Name
  arguments : List Argument
  selectionSet : List Selection
deriving Repr

-- Spec 6.3.2 collected fields map: partial list-backed ordered map insertion by response
-- name.
def addExecutableField (field : ExecutableField) :
    List (Name × List ExecutableField) -> List (Name × List ExecutableField)
  | [] => [(field.responseName, [field])]
  | (responseName, fields) :: rest =>
      if responseName == field.responseName then
        (responseName, fields ++ [field]) :: rest
      else
        (responseName, fields) :: addExecutableField field rest

-- Spec 6.3.2 collected fields map helper: inserts all fields into a response-name group
-- map.
def addExecutableFields (fields : List ExecutableField)
    (groups : List (Name × List ExecutableField)) :
    List (Name × List ExecutableField) :=
  fields.foldl (fun grouped field => addExecutableField field grouped) groups

-- Spec 6.3.2 collected fields map helper: inserts one existing group into another map.
def addExecutableGroup (group : Name × List ExecutableField) :
    List (Name × List ExecutableField) -> List (Name × List ExecutableField) :=
  addExecutableFields group.snd

-- Spec 6.3.2 `CollectFields` grouping merge for list-backed response-name maps.
def mergeExecutableGroups (left right : List (Name × List ExecutableField)) :
    List (Name × List ExecutableField) :=
  right.foldl (fun grouped group => addExecutableGroup group grouped) left

-- Spec 6.4.3 `CompleteValue` subfield merge: all collected fields for a response name
-- contribute their child selections.
def mergedFieldSelectionSet : List ExecutableField -> List Selection
  | [] => []
  | field :: rest => field.selectionSet ++ mergedFieldSelectionSet rest

-- Spec 6.3 `ExecuteRootSelectionSet`, 6.3.2 `CollectFields`, 6.3.3
-- `ExecuteCollectedFields`, 6.4 `ExecuteField`, and 6.4.3 `CompleteValue`: partial
-- depth-bounded execution model without coercion or error propagation.
mutual
  -- Spec 6.4.3 `CompleteValue`: partial; ignores declared `fieldType` wrappers and result
  -- coercion/errors, using the runtime value shape instead.
  def completeValue (schema : Schema) (resolvers : Resolvers)
      (variableValues : VariableValues) :
      Nat -> Name -> List Selection -> Value -> Response
    | 0, _parentType, _selectionSet, value => shallowResponse value
    | _depth + 1, _parentType, _selectionSet, .null => .null
    | _depth + 1, _parentType, _selectionSet, .scalar value => .scalar value
    | depth + 1, _parentType, selectionSet, source@(.object runtimeType _identity) =>
        .object (executeSelectionSet schema resolvers variableValues
          depth runtimeType source selectionSet)
    | depth + 1, parentType, selectionSet, .list values =>
        .list (values.map
          (fun value =>
            completeValue schema resolvers variableValues
              depth parentType selectionSet value))

  -- Spec 6.3.1 `ExecuteRootSelectionSet` / recursive selection-set execution: partial;
  -- directly returns data fields and omits error collection.
  def executeSelectionSet (schema : Schema) (resolvers : Resolvers)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : Value) :
      List Selection -> List (Name × Response)
    | selectionSet =>
        executeCollectedFields schema resolvers variableValues depth source
          (collectFields schema variableValues parentType source selectionSet)

  -- Spec 6.3.2 `CollectFields` selection step: partial; handles built-in directives and
  -- inline fragments.
  def collectSelection (schema : Schema) (variableValues : VariableValues) :
      Name -> Value -> Selection ->
        List (Name × List ExecutableField)
    | parentType, _source, .field responseName fieldName arguments directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives then
          [(responseName, [{
            parentType := parentType,
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            selectionSet := selectionSet
          }])]
        else
          []
    | parentType, source, .inlineFragment none directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives then
          collectFields schema variableValues parentType source selectionSet
        else
          []
    | parentType, source, .inlineFragment (some typeCondition) directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives then
          if doesFragmentTypeApplyBool schema parentType source typeCondition then
            collectFields schema variableValues parentType source selectionSet
          else
            []
        else
          []

  -- Spec 6.3.2 `CollectFields`: partial; list-backed ordered grouping of executable
  -- fields by response name.
  def collectFields (schema : Schema) (variableValues : VariableValues) :
      Name -> Value -> List Selection ->
        List (Name × List ExecutableField)
    | _parentType, _source, [] => []
    | parentType, source, selection :: rest =>
        mergeExecutableGroups
          (collectSelection schema variableValues parentType source selection)
          (collectFields schema variableValues parentType source rest)

  -- Spec 6.4 `ExecuteField`: partial; resolves one grouped response name once and
  -- completes with merged subselections.
  def executeField (schema : Schema) (resolvers : Resolvers)
      (variableValues : VariableValues) (depth : Nat) (source : Value)
      (responseName : Name) : List ExecutableField -> List (Name × Response)
    | [] => []
    | field :: fields =>
        match depth with
        | 0 => []
        | depth' + 1 =>
            let resolved :=
              resolvers.resolve field.parentType field.fieldName field.arguments source
            let childType :=
              (schema.fieldReturnType? field.parentType field.fieldName).getD field.fieldName
            let selectionSet := mergedFieldSelectionSet (field :: fields)
            [(responseName,
              completeValue schema resolvers variableValues
                depth' childType selectionSet resolved)]

  -- Spec 6.3.3 `ExecuteCollectedFields`: partial; executes each response-name group in
  -- stored order, without serial/parallel distinction or errors.
  def executeCollectedFields (schema : Schema) (resolvers : Resolvers)
      (variableValues : VariableValues) (depth : Nat) (source : Value) :
      List (Name × List ExecutableField) -> List (Name × Response)
    | [] => []
    | (responseName, fields) :: rest =>
        executeField schema resolvers variableValues depth source responseName fields
          ++ executeCollectedFields schema resolvers variableValues depth source rest
end

-- Local recursion-depth bound for the partial `ExecuteQuery` model.
def executeQueryDepthBound (operation : Operation) : Nat :=
  operation.size * 3 + 1

-- Spec 6.2.1 root execution expects a runtime object matching the operation root type.
-- The model still accepts arbitrary host values, but non-root sources execute to empty
-- data so equivalence statements are not forced to account for invalid roots.
def rootSourceAppliesBool (schema : Schema) (operation : Operation)
    (source : Value) : Bool :=
  match runtimeObjectType? source with
  | some objectName => schema.typeIncludesObjectBool operation.rootType objectName
  | none => false

-- Spec 6.2.1 `ExecuteQuery` / 6.3.1 `ExecuteRootSelectionSet`: partial; executes a
-- query operation as normal data-only object response.
def executeQuery (schema : Schema) (resolvers : Resolvers)
    (variableValues : VariableValues) (operation : Operation)
    (source : Value) : Response :=
  if rootSourceAppliesBool schema operation source then
    .object (executeSelectionSet schema resolvers variableValues
      (executeQueryDepthBound operation) operation.rootType source operation.selectionSet)
  else
    .object []

end Execution

end GraphQL
