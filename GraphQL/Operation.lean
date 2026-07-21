import GraphQL.Schema

/-! GraphQL operation representation
Spec reference: GraphQL September 2025.
- 2.3-2.4 Documents and Operations: this file models a single query-like operation, not
  a full executable document with multiple operations or operation kinds.
- 2.5-2.9 Selection Sets, Fields, Arguments, Aliases, and inline fragments: selection
  syntax is represented structurally, with aliases encoded as `responseName`.
- 2.10-2.13 Values, Variables, Type References, and Directives: variables and only the
  built-in executable directives `@skip` and `@include` are modeled.
- Fidelity note: named fragment definitions and fragment spreads are intentionally out of
  scope. This keeps the core closer to GraphCoQL's query fragment and avoids a separate
  fragment-expansion semantic layer.
-/

namespace GraphQL

-- Spec 2.7 `Argument`: faithful shape for a name/value pair; directive arguments are only
-- modeled for built-ins elsewhere.
structure Argument where
  name : Name
  value : InputValue
deriving Repr

namespace Argument

-- Spec 5.3.2 field argument comparison: arguments are a set by name; source order is not
-- semantically relevant.
def equivalent (left right : Argument) : Prop :=
  left.name = right.name ∧ left.value.equivalent right.value

-- Spec 5.3.2 field argument comparison lifted to argument lists as unordered sets by
-- argument name.
def argumentsEquivalent (left right : List Argument) : Prop :=
  (∀ argument,
    argument ∈ left -> ∃ argument', argument' ∈ right ∧ argument.equivalent argument')
  ∧ (∀ argument,
      argument ∈ right -> ∃ argument', argument' ∈ left ∧ argument'.equivalent argument)

end Argument

-- Spec 2.11 `VariableDefinition`: partial; name, type, and default are represented, but
-- descriptions and directives are omitted.
structure VariableDefinition where
  name : Name
  typeRef : TypeRef
  defaultValue : Option ConstInputValue := none
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
-- here and handled more faithfully by `Execution.directiveAllowsSelectionBool`.
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

-- Spec 3.13.1/3.13.2 directive runtime meaning lifted to directive lists.
def directivesAllow (directives : List DirectiveApplication) : Prop :=
  ∀ directive, directive ∈ directives -> directive.allows

-- Boolean counterpart to `directivesAllow`.
def directivesAllowBool (directives : List DirectiveApplication) : Bool :=
  directives.all (fun directive => directive.allowsBool)

-- Spec 2.5 `SelectionSet`, 2.6 `Field`, 2.8 `Alias`, and 2.9.2 `InlineFragment`:
-- partial; source grammar, named fragment spreads, and custom directives are omitted,
-- aliases are precomputed into response names.
inductive Selection where
  | field
    (responseName : Name)
    (fieldName : Name)
    (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection)
  | inlineFragment
    (typeCondition : Option Name)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection)
deriving Repr

-- Spec 2.4 `OperationDefinition`: partial; operation kind and document-level operation
-- selection are omitted, with `rootType` standing in for the selected root operation
-- type.
structure Operation where
  name : Option Name := none
  rootType : Name
  variableDefinitions : List VariableDefinition := []
  selectionSet : List Selection
deriving Repr

mutual
  -- Non-spec structural metric used by recursive operation transformations.
  def Selection.size : Selection -> Nat
    | .field _ _ _ _ selectionSet => 1 + SelectionSet.size selectionSet
    | .inlineFragment _ _ selectionSet => 1 + SelectionSet.size selectionSet

  def SelectionSet.size : List Selection -> Nat
    | [] => 0
    | selection :: rest => selection.size + SelectionSet.size rest
end

-- Non-spec structural metric over operation selections.
def Operation.size (operation : Operation) : Nat :=
  SelectionSet.size operation.selectionSet

namespace Selection

-- Spec 2.8 `Alias` / response name: faithful for fields; non-field selections have no
-- response name.
def responseName? : Selection -> Option Name
  | .field responseName _fieldName _arguments _directives _selectionSet =>
      some responseName
  | _ => none

-- Spec 6.3.2 `CollectSubfields`: partial helper exposing a selection's nested selection
-- set.
def subselections : Selection -> List Selection
  | .field _responseName _fieldName _arguments _directives selectionSet => selectionSet
  | .inlineFragment _typeCondition _directives selectionSet => selectionSet

-- Spec 6.3.2 `CollectFields` helper: recognizes field selections.
def isField : Selection -> Prop
  | .field .. => True
  | _ => False

-- Spec 6.3.2 `CollectFields` helper: recognizes inline-fragment selections.
def isInlineFragment : Selection -> Prop
  | .inlineFragment .. => True
  | _ => False

end Selection

namespace SelectionSet

-- Spec 6.3.2 field collection groups by response name: partial helper that only filters
-- direct fields and does not traverse inline fragments.
def fieldsWithResponseName (responseName : Name) (selectionSet : List Selection)
    : List Selection :=
  selectionSet.filter
    (fun selection =>
      match selection.responseName? with
      | some name => name == responseName
      | none => false)

-- Spec 6.3.2 field collection helper: removes direct fields with one response name.
def withoutFieldSelectionsWithResponseName (responseName : Name)
    (selectionSet : List Selection)
    : List Selection :=
  selectionSet.filter
    (fun selection =>
      match selection.responseName? with
      | some name => !(name == responseName)
      | none => true)

-- Spec 6.3.2 `CollectSubfields` analogue: concatenates nested selection sets.
def mergeSelectionSets (selections : List Selection) : List Selection :=
  selections.foldl (fun merged selection => merged ++ selection.subselections) []

end SelectionSet

end GraphQL
