import GraphQL.FieldMerge

namespace GraphQL

namespace Validation

def fragmentNamed? (fragments : List FragmentDefinition) (name : Name) : Option FragmentDefinition :=
  fragments.find? (fun fragment => fragment.name == name)

def directivesValid (_directives : List DirectiveApplication) : Prop :=
  True

def variableDefinitionNamed? (variableDefinitions : List VariableDefinition)
    (name : Name) : Option VariableDefinition :=
  variableDefinitions.find? (fun variableDefinition => variableDefinition.name == name)

def inputValueValid (schema : Schema) (variableDefinitions : List VariableDefinition)
    (value : InputValue) (expectedType : TypeRef) : Prop :=
  expectedType.validInput schema
    ∧ match value with
      | .variable variableName =>
          ∃ variableDefinition,
            variableDefinitionNamed? variableDefinitions variableName = some variableDefinition
      | _ => True

def variableDefinitionValid (schema : Schema)
    (variableDefinition : VariableDefinition) : Prop :=
  variableDefinition.typeRef.validInput schema
    ∧ match variableDefinition.defaultValue with
      | none => True
      | some defaultValue => inputValueValid schema [] defaultValue variableDefinition.typeRef

def variableDefinitionsValid (schema : Schema)
    (variableDefinitions : List VariableDefinition) : Prop :=
  (variableDefinitions.map VariableDefinition.name).Nodup
    ∧ ∀ variableDefinition, variableDefinition ∈ variableDefinitions ->
      variableDefinitionValid schema variableDefinition

def argumentValid (schema : Schema) (definitions : List InputValueDefinition)
    (variableDefinitions : List VariableDefinition) (argument : Argument) : Prop :=
  ∃ definition,
    Schema.lookupArgumentDefinition definitions argument.name = some definition
      ∧ inputValueValid schema variableDefinitions argument.value definition.inputType

def argumentNamed? (arguments : List Argument) (name : Name) : Option Argument :=
  arguments.find? (fun argument => argument.name == name)

def argumentDefinitionRequired (definition : InputValueDefinition) : Prop :=
  match definition.inputType with
  | .nonNull _ => definition.defaultValue = none
  | _ => False

def argumentsValid (schema : Schema) (definitions : List InputValueDefinition)
    (variableDefinitions : List VariableDefinition) (arguments : List Argument) : Prop :=
  (arguments.map Argument.name).Nodup
    ∧ (∀ argument, argument ∈ arguments ->
      argumentValid schema definitions variableDefinitions argument)
    ∧ (∀ definition, definition ∈ definitions ->
      argumentDefinitionRequired definition ->
        ∃ argument,
          argumentNamed? arguments definition.name = some argument)

def fragmentsSize (fragments : List FragmentDefinition) : Nat :=
  fragments.foldl (fun total fragment => total + fragment.size) 0

mutual
  def selectionValid (schema : Schema) (fragments : List FragmentDefinition)
      (variableDefinitions : List VariableDefinition) (parentType : Name) : Selection -> Prop
    | .field _responseName fieldName arguments directives selectionSet =>
        directivesValid directives
          ∧ ∃ fieldDefinition,
            schema.lookupField parentType fieldName = some fieldDefinition
              ∧ argumentsValid schema fieldDefinition.arguments variableDefinitions arguments
              ∧ fieldSelectionSetValid schema fragments variableDefinitions fieldDefinition selectionSet
    | .fragmentSpread fragmentName directives =>
        directivesValid directives
          ∧ ∃ fragmentDefinition,
            fragmentNamed? fragments fragmentName = some fragmentDefinition
              ∧ schema.typesOverlap parentType fragmentDefinition.typeCondition
    | .inlineFragment none directives selectionSet =>
        directivesValid directives
          ∧ selectionSet ≠ []
          ∧ selectionSetValid schema fragments variableDefinitions parentType selectionSet
    | .inlineFragment (some typeCondition) directives selectionSet =>
        directivesValid directives
          ∧ schema.compositeType typeCondition
          ∧ schema.typesOverlap parentType typeCondition
          ∧ selectionSet ≠ []
          ∧ selectionSetValid schema fragments variableDefinitions typeCondition selectionSet

  def selectionSetValid (schema : Schema) (fragments : List FragmentDefinition)
      (variableDefinitions : List VariableDefinition)
      (parentType : Name) (selectionSet : List Selection) : Prop :=
    ∀ selection, selection ∈ selectionSet ->
      selectionValid schema fragments variableDefinitions parentType selection

  def fieldSelectionSetValid (schema : Schema) (fragments : List FragmentDefinition)
      (variableDefinitions : List VariableDefinition)
      (fieldDefinition : FieldDefinition) (selectionSet : List Selection) : Prop :=
    let returnType := fieldDefinition.outputType.namedType
    fieldDefinition.outputType.validOutput schema
      ∧ ((schema.leafType returnType ∧ selectionSet = [])
      ∨ (schema.compositeType returnType
        ∧ selectionSet ≠ []
        ∧ selectionSetValid schema fragments variableDefinitions returnType selectionSet))
end

def fragmentValid (schema : Schema) (fragments : List FragmentDefinition)
    (variableDefinitions : List VariableDefinition)
    (fragment : FragmentDefinition) : Prop :=
  schema.compositeType fragment.typeCondition
    ∧ fragment.selectionSet ≠ []
    ∧ selectionSetValid schema fragments variableDefinitions
      fragment.typeCondition fragment.selectionSet
    ∧ FieldMerge.selectionSetFieldsCanMerge schema fragments
      (fragment.size + fragmentsSize fragments)
      fragment.typeCondition fragment.selectionSet

def operationValid (schema : Schema) (operation : Operation) : Prop :=
  operation.rootType = schema.queryType
    ∧ schema.compositeType operation.rootType
    ∧ variableDefinitionsValid schema operation.variableDefinitions
    ∧ operation.selectionSet ≠ []
    ∧ selectionSetValid schema operation.fragments operation.variableDefinitions
      operation.rootType operation.selectionSet
    ∧ FieldMerge.selectionSetFieldsCanMerge schema operation.fragments operation.size
      operation.rootType operation.selectionSet
    ∧ ∀ fragment, fragment ∈ operation.fragments ->
      fragmentValid schema operation.fragments operation.variableDefinitions fragment

end Validation

end GraphQL
