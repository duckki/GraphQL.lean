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

def responseForValue : Value -> List (Name × Response) -> Response
  | .null, _ => .null
  | .scalar value, [] => .scalar value
  | .scalar _value, fields => .object fields
  | .object _typeName _identity, fields => .object fields
  | .list values, fields =>
      .list (values.map (fun value => responseForValue value fields))

def runtimeObjectType? : Value -> Option Name
  | .object typeName _identity => some typeName
  | _ => none

def typeConditionAppliesBool (schema : Schema) (parentType : Name)
    (source : Value) (typeCondition : Name) : Bool :=
  match runtimeObjectType? source with
  | some objectName => schema.typeIncludesObjectBool typeCondition objectName
  | none => schema.typesOverlapBool parentType typeCondition

mutual
  def executeSelection (schema : Schema) (resolvers : Resolvers) (fragments : List FragmentDefinition)
      (fuel : Nat) (parentType : Name) (source : Value) : Selection -> List (Name × Response)
    | .field responseName fieldName arguments directives selectionSet =>
        if directivesAllowBool directives then
          let resolved := resolvers.resolve parentType fieldName arguments source
          let childType := (schema.fieldReturnType? parentType fieldName).getD fieldName
          let childFields := executeSelectionSet schema resolvers fragments fuel childType resolved selectionSet
          [(responseName, responseForValue resolved childFields)]
        else
          []
    | .fragmentSpread fragmentName directives =>
        if directivesAllowBool directives then
          match fuel with
          | 0 => []
          | fuel' + 1 =>
              match Validation.fragmentNamed? fragments fragmentName with
              | none => []
              | some fragment =>
                  if typeConditionAppliesBool schema parentType source fragment.typeCondition then
                    executeSelectionSet schema resolvers fragments fuel'
                      fragment.typeCondition source fragment.selectionSet
                  else
                    []
        else
          []
    | .inlineFragment none directives selectionSet =>
        if directivesAllowBool directives then
          executeSelectionSet schema resolvers fragments fuel parentType source selectionSet
        else
          []
    | .inlineFragment (some typeCondition) directives selectionSet =>
        if directivesAllowBool directives then
          if typeConditionAppliesBool schema parentType source typeCondition then
            executeSelectionSet schema resolvers fragments fuel typeCondition source selectionSet
          else
            []
        else
          []

  def executeSelectionSet (schema : Schema) (resolvers : Resolvers) (fragments : List FragmentDefinition)
      (fuel : Nat) (parentType : Name) (source : Value) : List Selection -> List (Name × Response)
    | [] => []
    | selection :: rest =>
        executeSelection schema resolvers fragments fuel parentType source selection
          ++ executeSelectionSet schema resolvers fragments fuel parentType source rest
end

def executeOperation (schema : Schema) (resolvers : Resolvers) (operation : Operation)
    (source : Value) : Response :=
  .object (executeSelectionSet schema resolvers operation.fragments operation.size
    operation.rootType source operation.selectionSet)

end Execution

end GraphQL
