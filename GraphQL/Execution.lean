import GraphQL.Semantic

namespace GraphQL

namespace Execution

inductive Value where
  | null
  | scalar (value : String)
  | object (typeName : Name) (identity : Nat)
  | list (values : List Value)
deriving Repr

inductive Response where
  | null
  | scalar (value : String)
  | object (fields : List (Name × Response))
  | list (values : List Response)
deriving Repr

structure Resolvers where
  resolve : Name -> Name -> List Argument -> Value -> Value

abbrev VariableValues := List (Name × InputValue)

def lookupVariableValue? (variableValues : VariableValues) (name : Name) : Option InputValue :=
  match variableValues with
  | [] => none
  | (variableName, value) :: rest =>
      if variableName = name then some value else lookupVariableValue? rest name

def inputValueBoolean? (variableValues : VariableValues) : InputValue -> Option Bool
  | .variable name => do
      let value <- lookupVariableValue? variableValues name
      value.staticBoolean?
  | value => value.staticBoolean?

def directiveAllowsBool (variableValues : VariableValues) : DirectiveApplication -> Bool
  | .skip ifArgument =>
      match inputValueBoolean? variableValues ifArgument with
      | some value => !value
      | none => false
  | .include ifArgument =>
      match inputValueBoolean? variableValues ifArgument with
      | some value => value
      | none => false

def directivesAllowWithVariablesBool (variableValues : VariableValues)
    (directives : List DirectiveApplication) : Bool :=
  directives.all (fun directive => directiveAllowsBool variableValues directive)

def shallowResponse : Value -> Response
  | .null => .null
  | .scalar value => .scalar value
  | .object _typeName _identity => .object []
  | .list values => .list (values.map shallowResponse)

def runtimeObjectType? : Value -> Option Name
  | .object typeName _identity => some typeName
  | _ => none

def typeConditionAppliesBool (schema : Schema) (parentType : Name)
    (source : Value) (typeCondition : Name) : Bool :=
  match runtimeObjectType? source with
  | some objectName => schema.typeIncludesObjectBool typeCondition objectName
  | none => schema.typesOverlapBool parentType typeCondition

structure ExecutableField where
  parentType : Name
  responseName : Name
  fieldName : Name
  arguments : List Argument
  selectionSet : List Semantic.Selection
deriving Repr

def addExecutableField (field : ExecutableField) :
    List (Name × List ExecutableField) -> List (Name × List ExecutableField)
  | [] => [(field.responseName, [field])]
  | (responseName, fields) :: rest =>
      if responseName == field.responseName then
        (responseName, fields ++ [field]) :: rest
      else
        (responseName, fields) :: addExecutableField field rest

def addExecutableFields (fields : List ExecutableField)
    (groups : List (Name × List ExecutableField)) :
    List (Name × List ExecutableField) :=
  fields.foldl (fun grouped field => addExecutableField field grouped) groups

def addExecutableGroup (group : Name × List ExecutableField) :
    List (Name × List ExecutableField) -> List (Name × List ExecutableField) :=
  addExecutableFields group.snd

def mergeExecutableGroups (left right : List (Name × List ExecutableField)) :
    List (Name × List ExecutableField) :=
  right.foldl (fun grouped group => addExecutableGroup group grouped) left

def mergedFieldSelectionSet : List ExecutableField -> List Semantic.Selection
  | [] => []
  | field :: rest => field.selectionSet ++ mergedFieldSelectionSet rest

mutual
  def completeValue (schema : Schema) (resolvers : Resolvers)
      (variableValues : VariableValues) :
      Nat -> Name -> List Semantic.Selection -> Value -> Response
    | 0, _parentType, _selectionSet, value => shallowResponse value
    | _fuel + 1, _parentType, _selectionSet, .null => .null
    | _fuel + 1, _parentType, _selectionSet, .scalar value => .scalar value
    | fuel + 1, _parentType, selectionSet, source@(.object runtimeType _identity) =>
        .object (executeSelectionSet schema resolvers variableValues
          fuel runtimeType source selectionSet)
    | fuel + 1, parentType, selectionSet, .list values =>
        .list (values.map
          (fun value =>
            completeValue schema resolvers variableValues
              fuel parentType selectionSet value))

  def executeSelectionSet (schema : Schema) (resolvers : Resolvers)
      (variableValues : VariableValues)
      (fuel : Nat) (parentType : Name) (source : Value) :
      List Semantic.Selection -> List (Name × Response)
    | selectionSet =>
        executeGroupedFieldSet schema resolvers variableValues fuel source
          (collectFields schema variableValues fuel parentType source selectionSet)

  def collectSelection (schema : Schema) (variableValues : VariableValues) :
      Nat -> Name -> Value -> Semantic.Selection ->
        List (Name × List ExecutableField)
    | 0, _parentType, _source, _selection => []
    | _fuel + 1, parentType, _source,
        .field responseName fieldName arguments directives selectionSet =>
        if directivesAllowWithVariablesBool variableValues directives then
          [(responseName, [{
            parentType := parentType,
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            selectionSet := selectionSet
          }])]
        else
          []
    | fuel + 1, parentType, source, .inlineFragment none directives selectionSet =>
        if directivesAllowWithVariablesBool variableValues directives then
          collectFields schema variableValues fuel parentType source selectionSet
        else
          []
    | fuel + 1, parentType, source,
        .inlineFragment (some typeCondition) directives selectionSet =>
        if directivesAllowWithVariablesBool variableValues directives then
          if typeConditionAppliesBool schema parentType source typeCondition then
            collectFields schema variableValues fuel typeCondition source selectionSet
          else
            []
        else
          []

  def collectFields (schema : Schema) (variableValues : VariableValues) :
      Nat -> Name -> Value -> List Semantic.Selection ->
        List (Name × List ExecutableField)
    | 0, _parentType, _source, _selectionSet => []
    | _fuel + 1, _parentType, _source, [] => []
    | fuel + 1, parentType, source, selection :: rest =>
        mergeExecutableGroups
          (collectSelection schema variableValues (fuel + 1) parentType source selection)
          (collectFields schema variableValues (fuel + 1) parentType source rest)

  def executeGroupedField (schema : Schema) (resolvers : Resolvers)
      (variableValues : VariableValues) (fuel : Nat) (source : Value)
      (responseName : Name) : List ExecutableField -> List (Name × Response)
    | [] => []
    | field :: fields =>
        match fuel with
        | 0 => []
        | fuel' + 1 =>
            let resolved :=
              resolvers.resolve field.parentType field.fieldName field.arguments source
            let childType :=
              (schema.fieldReturnType? field.parentType field.fieldName).getD field.fieldName
            let selectionSet := mergedFieldSelectionSet (field :: fields)
            [(responseName,
              completeValue schema resolvers variableValues
                fuel' childType selectionSet resolved)]

  def executeGroupedFieldSet (schema : Schema) (resolvers : Resolvers)
      (variableValues : VariableValues) (fuel : Nat) (source : Value) :
      List (Name × List ExecutableField) -> List (Name × Response)
    | [] => []
    | (responseName, fields) :: rest =>
        executeGroupedField schema resolvers variableValues fuel source responseName fields
          ++ executeGroupedFieldSet schema resolvers variableValues fuel source rest
end

def semanticExecutionFuel (operation : Semantic.Operation) : Nat :=
  operation.size * 3 + 1

def executeSemanticOperation (schema : Schema) (resolvers : Resolvers)
    (variableValues : VariableValues) (operation : Semantic.Operation)
    (source : Value) : Response :=
  .object (executeSelectionSet schema resolvers variableValues
    (semanticExecutionFuel operation) operation.rootType source operation.selectionSet)

def executionFuel (operation : Operation) : Nat :=
  semanticExecutionFuel (Semantic.fromOperation operation)

def executeOperation (schema : Schema) (resolvers : Resolvers)
    (variableValues : VariableValues) (operation : Operation)
    (source : Value) : Response :=
  executeSemanticOperation schema resolvers variableValues
    (Semantic.fromOperation operation) source

end Execution

end GraphQL
