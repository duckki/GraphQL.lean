import GraphQL.Schema

namespace GraphQL

namespace Validation

def fragmentNamed? (fragments : List FragmentDefinition) (name : Name) : Option FragmentDefinition :=
  fragments.find? (fun fragment => fragment.name == name)

def directivesValid (_directives : List DirectiveApplication) : Prop :=
  True

mutual
  def selectionValid (schema : Schema) (fragments : List FragmentDefinition)
      (parentType : Name) : Selection -> Prop
    | .field _responseName fieldName directives selectionSet =>
        directivesValid directives
          ∧ ∃ fieldDefinition,
            schema.lookupField parentType fieldName = some fieldDefinition
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
    let returnType := fieldDefinition.typeRef.namedType
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
