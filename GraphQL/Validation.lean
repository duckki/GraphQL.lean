import GraphQL.Schema

namespace GraphQL

namespace Validation

def fragmentNamed? (fragments : List FragmentDefinition) (name : Name) : Option FragmentDefinition :=
  fragments.find? (fun fragment => fragment.name == name)

def directivesValid (_directives : List DirectiveApplication) : Prop :=
  True

def inputValueValid (schema : Schema) (_value : InputValue) (expectedType : TypeRef) : Prop :=
  schema.inputType expectedType.namedType

def argumentValid (schema : Schema) (definitions : List InputValueDefinition)
    (argument : Argument) : Prop :=
  ∃ definition,
    Schema.lookupArgumentDefinition definitions argument.name = some definition
      ∧ inputValueValid schema argument.value definition.inputType

def argumentsValid (schema : Schema) (definitions : List InputValueDefinition)
    (arguments : List Argument) : Prop :=
  ∀ argument, argument ∈ arguments -> argumentValid schema definitions argument

mutual
  def selectionValid (schema : Schema) (fragments : List FragmentDefinition)
      (parentType : Name) : Selection -> Prop
    | .field _responseName fieldName arguments directives selectionSet =>
        directivesValid directives
          ∧ ∃ fieldDefinition,
            schema.lookupField parentType fieldName = some fieldDefinition
              ∧ argumentsValid schema fieldDefinition.arguments arguments
              ∧ fieldSelectionSetValid schema fragments fieldDefinition selectionSet
    | .fragmentSpread fragmentName directives =>
        directivesValid directives
          ∧ ∃ fragmentDefinition,
            fragmentNamed? fragments fragmentName = some fragmentDefinition
              ∧ schema.typesOverlap parentType fragmentDefinition.typeCondition
    | .inlineFragment none directives selectionSet =>
        directivesValid directives
          ∧ selectionSetValid schema fragments parentType selectionSet
    | .inlineFragment (some typeCondition) directives selectionSet =>
        directivesValid directives
          ∧ schema.compositeType typeCondition
          ∧ schema.typesOverlap parentType typeCondition
          ∧ selectionSetValid schema fragments typeCondition selectionSet

  def selectionSetValid (schema : Schema) (fragments : List FragmentDefinition)
      (parentType : Name) (selectionSet : List Selection) : Prop :=
    ∀ selection, selection ∈ selectionSet -> selectionValid schema fragments parentType selection

  def fieldSelectionSetValid (schema : Schema) (fragments : List FragmentDefinition)
      (fieldDefinition : FieldDefinition) (selectionSet : List Selection) : Prop :=
    let returnType := fieldDefinition.outputType.namedType
    (schema.leafType returnType ∧ selectionSet = [])
      ∨ (schema.compositeType returnType
        ∧ selectionSetValid schema fragments returnType selectionSet)
end

def fragmentValid (schema : Schema) (fragments : List FragmentDefinition)
    (fragment : FragmentDefinition) : Prop :=
  schema.compositeType fragment.typeCondition
    ∧ selectionSetValid schema fragments fragment.typeCondition fragment.selectionSet

def operationValid (schema : Schema) (operation : Operation) : Prop :=
  operation.rootType = schema.queryType
    ∧ schema.compositeType operation.rootType
    ∧ selectionSetValid schema operation.fragments operation.rootType operation.selectionSet
    ∧ ∀ fragment, fragment ∈ operation.fragments -> fragmentValid schema operation.fragments fragment

end Validation

end GraphQL
