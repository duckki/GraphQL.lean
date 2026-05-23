import GraphQL.Validation
import GraphQL.ResponseShape

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

mutual
  def completeValue (schema : Schema) (resolvers : Resolvers)
      (variableValues : VariableValues) (fragments : List FragmentDefinition) :
      Nat -> Name -> List Selection -> Value -> Response
    | 0, _parentType, _selectionSet, value => shallowResponse value
    | _fuel + 1, _parentType, _selectionSet, .null => .null
    | _fuel + 1, _parentType, _selectionSet, .scalar value => .scalar value
    | fuel + 1, _parentType, selectionSet, source@(.object runtimeType _identity) =>
        .object (executeSelectionSet schema resolvers variableValues fragments
          fuel runtimeType source selectionSet)
    | fuel + 1, parentType, selectionSet, .list values =>
        .list (values.map
          (fun value =>
            completeValue schema resolvers variableValues fragments
              fuel parentType selectionSet value))

  def executeSelection (schema : Schema) (resolvers : Resolvers)
      (variableValues : VariableValues) (fragments : List FragmentDefinition)
      (fuel : Nat) (parentType : Name) (source : Value) : Selection -> List (Name × Response)
    | .field responseName fieldName arguments directives selectionSet =>
        if directivesAllowWithVariablesBool variableValues directives then
          match fuel with
          | 0 => []
          | fuel' + 1 =>
              let resolved := resolvers.resolve parentType fieldName arguments source
              let childType := (schema.fieldReturnType? parentType fieldName).getD fieldName
              [(responseName,
                completeValue schema resolvers variableValues fragments
                  fuel' childType selectionSet resolved)]
        else
          []
    | .fragmentSpread fragmentName directives =>
        if directivesAllowWithVariablesBool variableValues directives then
          match fuel with
          | 0 => []
          | fuel' + 1 =>
              match Validation.fragmentNamed? fragments fragmentName with
              | none => []
              | some fragment =>
                  if typeConditionAppliesBool schema parentType source fragment.typeCondition then
                    executeSelectionSet schema resolvers variableValues fragments fuel'
                      fragment.typeCondition source fragment.selectionSet
                  else
                    []
        else
          []
    | .inlineFragment none directives selectionSet =>
        if directivesAllowWithVariablesBool variableValues directives then
          match fuel with
          | 0 => []
          | fuel' + 1 =>
              executeSelectionSet schema resolvers variableValues fragments
                fuel' parentType source selectionSet
        else
          []
    | .inlineFragment (some typeCondition) directives selectionSet =>
        if directivesAllowWithVariablesBool variableValues directives then
          match fuel with
          | 0 => []
          | fuel' + 1 =>
              if typeConditionAppliesBool schema parentType source typeCondition then
                executeSelectionSet schema resolvers variableValues fragments
                  fuel' typeCondition source selectionSet
              else
                []
        else
          []

  def executeSelectionSet (schema : Schema) (resolvers : Resolvers)
      (variableValues : VariableValues) (fragments : List FragmentDefinition)
      (fuel : Nat) (parentType : Name) (source : Value) : List Selection -> List (Name × Response)
    | [] => []
    | selection :: rest =>
        executeSelection schema resolvers variableValues fragments fuel parentType source selection
          ++ executeSelectionSet schema resolvers variableValues fragments fuel parentType source rest
end

def executionFuel (operation : Operation) : Nat :=
  operation.size * 3 + 1

def executeOperation (schema : Schema) (resolvers : Resolvers)
    (variableValues : VariableValues) (operation : Operation)
    (source : Value) : Response :=
  .object (executeSelectionSet schema resolvers variableValues operation.fragments
    (executionFuel operation) operation.rootType source operation.selectionSet)

end Execution

end GraphQL
