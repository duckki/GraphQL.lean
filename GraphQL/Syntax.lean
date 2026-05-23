namespace GraphQL

abbrev Name := String

inductive TypeRef where
  | named : Name -> TypeRef
  | list : TypeRef -> TypeRef
  | nonNull : TypeRef -> TypeRef
deriving Repr, DecidableEq

namespace TypeRef

def namedType : TypeRef -> Name
  | .named name => name
  | .list inner => inner.namedType
  | .nonNull inner => inner.namedType

end TypeRef

inductive InputValue where
  | null
  | int (value : Int)
  | float (value : String)
  | string (value : String)
  | boolean (value : Bool)
  | enum (value : Name)
  | list (values : List InputValue)
  | object (fields : List (Name × InputValue))
  | variable (name : Name)
deriving Repr

namespace InputValue

def staticBoolean? : InputValue -> Option Bool
  | .boolean value => some value
  | _ => none

end InputValue

structure Argument where
  name : Name
  value : InputValue
deriving Repr

structure VariableDefinition where
  name : Name
  typeRef : TypeRef
  defaultValue : Option InputValue := none
deriving Repr

inductive DirectiveApplication where
  | skip (ifArgument : InputValue)
  | include (ifArgument : InputValue)
deriving Repr

namespace DirectiveApplication

def allows : DirectiveApplication -> Prop
  | .skip ifArgument => ifArgument.staticBoolean? = some false
  | .include ifArgument => ifArgument.staticBoolean? = some true

def allowsBool : DirectiveApplication -> Bool
  | .skip ifArgument =>
      match ifArgument.staticBoolean? with
      | some value => !value
      | none => false
  | .include ifArgument =>
      match ifArgument.staticBoolean? with
      | some value => value
      | none => false

end DirectiveApplication

def directivesAllow (directives : List DirectiveApplication) : Prop :=
  ∀ directive, directive ∈ directives -> directive.allows

def directivesAllowBool (directives : List DirectiveApplication) : Bool :=
  directives.all (fun directive => directive.allowsBool)

inductive Selection where
  | field
      (responseName : Name)
      (fieldName : Name)
      (arguments : List Argument)
      (directives : List DirectiveApplication)
      (selectionSet : List Selection)
  | fragmentSpread
      (fragmentName : Name)
      (directives : List DirectiveApplication)
  | inlineFragment
      (typeCondition : Option Name)
      (directives : List DirectiveApplication)
      (selectionSet : List Selection)
deriving Repr

structure FragmentDefinition where
  name : Name
  typeCondition : Name
  selectionSet : List Selection
deriving Repr

structure Operation where
  name : Option Name := none
  rootType : Name
  variableDefinitions : List VariableDefinition := []
  selectionSet : List Selection
  fragments : List FragmentDefinition := []
deriving Repr

mutual
  def Selection.size : Selection -> Nat
    | .field _ _ _ _ selectionSet => 1 + SelectionSet.size selectionSet
    | .fragmentSpread _ _ => 1
    | .inlineFragment _ _ selectionSet => 1 + SelectionSet.size selectionSet

  def SelectionSet.size : List Selection -> Nat
    | [] => 0
    | selection :: rest => selection.size + SelectionSet.size rest
end

def FragmentDefinition.size (fragment : FragmentDefinition) : Nat :=
  SelectionSet.size fragment.selectionSet

def Operation.size (operation : Operation) : Nat :=
  SelectionSet.size operation.selectionSet
    + operation.fragments.foldl (fun total fragment => total + fragment.size) 0

mutual
  def Selection.fragmentFree : Selection -> Prop
    | .field _ _ _ _ selectionSet => SelectionSet.fragmentFree selectionSet
    | .fragmentSpread _ _ => False
    | .inlineFragment _ _ selectionSet => SelectionSet.fragmentFree selectionSet

  def SelectionSet.fragmentFree : List Selection -> Prop
    | [] => True
    | selection :: rest => selection.fragmentFree ∧ SelectionSet.fragmentFree rest
end

def Operation.fragmentFree (operation : Operation) : Prop :=
  operation.fragments = [] ∧ SelectionSet.fragmentFree operation.selectionSet

end GraphQL
