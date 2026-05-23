import GraphQL.Schema

/-!
Spec reference: GraphQL September 2025.
- 2.3-2.4 Documents and Operations: this file models a single operation plus its
  fragments, not a full executable document with multiple operations or operation kinds.
- 2.5-2.9 Selection Sets, Fields, Arguments, Aliases, and Fragments: field/fragment syntax
  is represented structurally, with aliases encoded as `responseName`.
- 2.10-2.13 Values, Variables, Type References, and Directives: variables and only the
  built-in executable directives `@skip` and `@include` are modeled.
-/
namespace GraphQL

-- Spec 2.7 `Argument`: faithful shape for a name/value pair; directive arguments are only
-- modeled for built-ins elsewhere.
structure Argument where
  name : Name
  value : InputValue
deriving Repr

-- Spec 2.11 `VariableDefinition`: partial; name, type, and default are represented, but
-- descriptions and directives are omitted.
structure VariableDefinition where
  name : Name
  typeRef : TypeRef
  defaultValue : Option InputValue := none
deriving Repr

-- Spec 3.13.1 `@skip` and 3.13.2 `@include`: partial; only these two built-in executable
-- directives are represented, not arbitrary/custom directives or directive locations.
inductive DirectiveApplication where
  | skip (ifArgument : InputValue)
  | include (ifArgument : InputValue)
deriving Repr

namespace DirectiveApplication

-- Spec 3.13.1/3.13.2 directive runtime meaning: partial; faithful only for statically
-- known Boolean literals, not variables.
def allows : DirectiveApplication -> Prop
  | .skip ifArgument => ifArgument.staticBoolean? = some false
  | .include ifArgument => ifArgument.staticBoolean? = some true

-- Spec 3.13.1/3.13.2 directive runtime meaning: partial; variables are treated as false
-- here and handled more faithfully by `Execution.directiveAllowsBool`.
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

-- Spec 2.5 `SelectionSet`, 2.6 `Field`, 2.8 `Alias`, 2.9 `FragmentSpread`, and 2.9.2
-- `InlineFragment`: partial; source grammar and custom directives are omitted, aliases
-- are precomputed into response names.
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

-- Spec 2.9 `FragmentDefinition`: partial; descriptions and directives on fragment
-- definitions are omitted.
structure FragmentDefinition where
  name : Name
  typeCondition : Name
  selectionSet : List Selection
deriving Repr

-- Spec 2.4 `OperationDefinition`: partial; operation kind and document-level operation
-- selection are omitted, with `rootType` standing in for the selected root operation
-- type.
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

-- Spec 2.9 fragments: non-spec helper used to identify operations already inlined or
-- fragment-free.
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

-- Spec 5.5.2.2 `DetectFragmentCycles` step "all fragment spread descendants": faithful as
-- a structural descendant-name collector for the modeled syntax.
mutual
  def Selection.fragmentSpreadNames : Selection -> List Name
    | .field _responseName _fieldName _arguments _directives selectionSet =>
        SelectionSet.fragmentSpreadNames selectionSet
    | .fragmentSpread fragmentName _directives => [fragmentName]
    | .inlineFragment _typeCondition _directives selectionSet =>
        SelectionSet.fragmentSpreadNames selectionSet

  def SelectionSet.fragmentSpreadNames : List Selection -> List Name
    | [] => []
    | selection :: rest =>
        selection.fragmentSpreadNames ++ SelectionSet.fragmentSpreadNames rest
end

def FragmentDefinition.fragmentSpreadNames (fragment : FragmentDefinition) : List Name :=
  SelectionSet.fragmentSpreadNames fragment.selectionSet

namespace Selection

-- Spec 2.8 `Alias` / response name: faithful for fields; non-field selections have no
-- response name.
def responseName? : Selection -> Option Name
  | .field responseName _fieldName _arguments _directives _selectionSet => some responseName
  | _ => none

-- Spec 6.3.2 `CollectSubfields`: partial helper exposing a selection's nested selection
-- set.
def subselections : Selection -> List Selection
  | .field _responseName _fieldName _arguments _directives selectionSet => selectionSet
  | .inlineFragment _typeCondition _directives selectionSet => selectionSet
  | .fragmentSpread _fragmentName _directives => []

def isField : Selection -> Prop
  | .field .. => True
  | _ => False

def isInlineFragment : Selection -> Prop
  | .inlineFragment .. => True
  | _ => False

end Selection

namespace SelectionSet

-- Spec 6.3.2 field collection groups by response name: partial helper that only filters
-- direct fields and does not traverse fragments.
def fieldsWithResponseName (responseName : Name) (selectionSet : List Selection) :
    List Selection :=
  selectionSet.filter (fun selection =>
    match selection.responseName? with
    | some name => name == responseName
    | none => false)

def withoutFieldsWithResponseName (responseName : Name) (selectionSet : List Selection) :
    List Selection :=
  selectionSet.filter (fun selection =>
    match selection.responseName? with
    | some name => !(name == responseName)
    | none => true)

def mergeSelectionSets (selections : List Selection) : List Selection :=
  selections.foldl (fun merged selection => merged ++ selection.subselections) []

end SelectionSet

namespace FragmentDefinition

-- Spec 5.5.2.1 Fragment Spread Target Defined: partial lookup helper for finding a target
-- fragment by name.
def find? (fragments : List FragmentDefinition) (name : Name) :
    Option FragmentDefinition :=
  fragments.find? (fun fragment => fragment.name == name)

end FragmentDefinition

end GraphQL
