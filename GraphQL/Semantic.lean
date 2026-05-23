import GraphQL.Operation

namespace GraphQL

namespace Semantic

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

structure Operation where
  name : Option Name := none
  rootType : Name
  variableDefinitions : List VariableDefinition := []
  selectionSet : List Selection
deriving Repr

mutual
  def Selection.size : Selection -> Nat
    | .field _responseName _fieldName _arguments _directives selectionSet =>
        1 + SelectionSet.size selectionSet
    | .inlineFragment _typeCondition _directives selectionSet =>
        1 + SelectionSet.size selectionSet

  def SelectionSet.size : List Selection -> Nat
    | [] => 0
    | selection :: rest => selection.size + SelectionSet.size rest
end

def Operation.size (operation : Operation) : Nat :=
  SelectionSet.size operation.selectionSet

namespace Selection

def responseName? : Selection -> Option Name
  | .field responseName _fieldName _arguments _directives _selectionSet =>
      some responseName
  | .inlineFragment .. => none

def subselections : Selection -> List Selection
  | .field _responseName _fieldName _arguments _directives selectionSet =>
      selectionSet
  | .inlineFragment _typeCondition _directives selectionSet =>
      selectionSet

def isField : Selection -> Prop
  | .field .. => True
  | _ => False

def isInlineFragment : Selection -> Prop
  | .inlineFragment .. => True
  | _ => False

end Selection

namespace SelectionSet

def fieldsWithResponseName (responseName : Name) (selectionSet : List Selection) :
    List Selection :=
  selectionSet.filter (fun selection =>
    match selection.responseName? with
    | some name => name == responseName
    | none => false)

def withoutFieldsWithResponseName (responseName : Name)
    (selectionSet : List Selection) : List Selection :=
  selectionSet.filter (fun selection =>
    match selection.responseName? with
    | some name => !(name == responseName)
    | none => true)

def mergeSelectionSets (selections : List Selection) : List Selection :=
  selections.foldl (fun merged selection => merged ++ selection.subselections) []

end SelectionSet

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

def inlineFuel (operation : GraphQL.Operation) : Nat :=
  operation.size + 1

def fromOperation (operation : GraphQL.Operation) : Operation :=
  {
    name := operation.name,
    rootType := operation.rootType,
    variableDefinitions := operation.variableDefinitions,
    selectionSet := inlineSelectionSet operation.fragments
      (inlineFuel operation) operation.selectionSet
  }

mutual
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
