import GraphQL.Operation

/-!
Spec reference: GraphQL September 2025.
- 2.9 Fragments and 5.5 Fragment validation: this module prepares a fragment-free semantic
  syntax by replacing named fragment spreads with inline fragments.
- 6.3.2 Field Collection: fragment inlining is a preprocessing analogue of the spec's
  recursive fragment traversal before later collection/execution.
- Fidelity note: this is not a spec-defined transformation. It assumes validation
  separately handles fragment existence and acyclicity; unresolved spreads become empty,
  and fragment-spread directives are preserved on the synthetic inline fragment.
-/
namespace GraphQL

namespace Semantic

-- Spec-derived syntax for 2.5/2.6/2.9.2 selections after named fragments are inlined;
-- partial because `FragmentSpread` is intentionally absent.
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

-- Spec-derived single-operation semantic form; partial for the same reasons as
-- `GraphQL.Operation`, with fragments removed.
structure Operation where
  name : Option Name := none
  rootType : Name
  variableDefinitions : List VariableDefinition := []
  selectionSet : List Selection
deriving Repr

mutual
  -- Non-spec structural metric used to fuel recursive semantic operations.
  def Selection.size : Selection -> Nat
    | .field _responseName _fieldName _arguments _directives selectionSet =>
        1 + SelectionSet.size selectionSet
    | .inlineFragment _typeCondition _directives selectionSet =>
        1 + SelectionSet.size selectionSet

  def SelectionSet.size : List Selection -> Nat
    | [] => 0
    | selection :: rest => selection.size + SelectionSet.size rest
end

-- Non-spec structural metric over fragment-free semantic operations.
def Operation.size (operation : Operation) : Nat :=
  SelectionSet.size operation.selectionSet

namespace Selection

-- Spec 2.8 response name: faithful for semantic fields; inline fragments produce no
-- response key.
def responseName? : Selection -> Option Name
  | .field responseName _fieldName _arguments _directives _selectionSet =>
      some responseName
  | .inlineFragment .. => none

-- Spec 6.3.2 `CollectSubfields`: partial helper exposing nested semantic selections.
def subselections : Selection -> List Selection
  | .field _responseName _fieldName _arguments _directives selectionSet =>
      selectionSet
  | .inlineFragment _typeCondition _directives selectionSet =>
      selectionSet

-- Spec 6.3.2 `CollectFields` helper over semantic selections.
def isField : Selection -> Prop
  | .field .. => True
  | _ => False

-- Spec 6.3.2 `CollectFields` helper over semantic inline fragments.
def isInlineFragment : Selection -> Prop
  | .inlineFragment .. => True
  | _ => False

end Selection

namespace SelectionSet

-- Spec 6.3.2 field collection groups by response name over semantic selections.
def fieldsWithResponseName (responseName : Name) (selectionSet : List Selection) :
    List Selection :=
  selectionSet.filter (fun selection =>
    match selection.responseName? with
    | some name => name == responseName
    | none => false)

-- Spec 6.3.2 field collection helper: removes semantic fields with one response name.
def withoutFieldsWithResponseName (responseName : Name)
    (selectionSet : List Selection) : List Selection :=
  selectionSet.filter (fun selection =>
    match selection.responseName? with
    | some name => !(name == responseName)
    | none => true)

-- Spec 6.3.2 `CollectSubfields` analogue over semantic selections.
def mergeSelectionSets (selections : List Selection) : List Selection :=
  selections.foldl (fun merged selection => merged ++ selection.subselections) []

end SelectionSet

-- Spec-related fragment expansion: non-spec preprocessing pass corresponding to
-- recursively traversing fragment spreads in validation/execution algorithms.
mutual
  def inlineSelection (fragments : List FragmentDefinition) :
      Nat -> GraphQL.Selection -> List Selection
    | 0, _selection => []
    | fuel + 1,
        .field responseName fieldName arguments directives selectionSet =>
        [.field responseName fieldName arguments directives
          (inlineSelectionSet fragments fuel selectionSet)]
    | fuel + 1, .fragmentSpread fragmentName directives =>
        match FragmentDefinition.find? fragments fragmentName with
        | none => []
        | some fragment =>
            [.inlineFragment (some fragment.typeCondition) directives
              (inlineSelectionSet fragments fuel fragment.selectionSet)]
    | fuel + 1, .inlineFragment typeCondition directives selectionSet =>
        [.inlineFragment typeCondition directives
          (inlineSelectionSet fragments fuel selectionSet)]

  def inlineSelectionSet (fragments : List FragmentDefinition) :
      Nat -> List GraphQL.Selection -> List Selection
    | 0, _selectionSet => []
    | _fuel + 1, [] => []
    | fuel + 1, selection :: rest =>
        inlineSelection fragments (fuel + 1) selection
          ++ inlineSelectionSet fragments (fuel + 1) rest
end

-- Non-spec structural fuel bound for named-fragment inlining.
def inlineFuel (operation : GraphQL.Operation) : Nat :=
  operation.size + 1

-- Spec 2.9 Fragment Spread semantics: partial; turns named spreads into inline fragments
-- with the fragment's type condition, assuming a validated acyclic fragment graph.
def fromOperation (operation : GraphQL.Operation) : Operation :=
  {
    name := operation.name,
    rootType := operation.rootType,
    variableDefinitions := operation.variableDefinitions,
    selectionSet := inlineSelectionSet operation.fragments
      (inlineFuel operation) operation.selectionSet
  }

mutual
  -- Spec-related erasure from semantic selections to fragment-free raw selections.
  def Selection.toOperationSelection : Selection -> GraphQL.Selection
    | .field responseName fieldName arguments directives selectionSet =>
        .field responseName fieldName arguments directives
          (SelectionSet.toOperationSelectionSet selectionSet)
    | .inlineFragment typeCondition directives selectionSet =>
        .inlineFragment typeCondition directives
          (SelectionSet.toOperationSelectionSet selectionSet)

  def SelectionSet.toOperationSelectionSet :
      List Selection -> List GraphQL.Selection
    | [] => []
    | selection :: rest =>
        selection.toOperationSelection :: SelectionSet.toOperationSelectionSet rest
end

-- Spec-related erasure back to operation syntax: non-spec helper that returns a
-- fragment-free raw operation.
def Operation.toOperation (operation : Operation) : GraphQL.Operation :=
  {
    name := operation.name,
    rootType := operation.rootType,
    variableDefinitions := operation.variableDefinitions,
    selectionSet := SelectionSet.toOperationSelectionSet operation.selectionSet,
    fragments := []
  }

end Semantic

end GraphQL
