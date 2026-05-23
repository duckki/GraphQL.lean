import GraphQL.FieldMerge

/-!
Spec reference: GraphQL September 2025.
- 5.2 Operations, 5.3 Fields, 5.4 Arguments, 5.5 Fragments, 5.6 Values, 5.7 Directives,
  and 5.8 Variables: this file states operation validity as a proposition over the modeled
  schema and operation syntax.
- Fidelity note: the model is intentionally partial. It omits document-level
  multi-operation rules, mutation/subscription rules, directive
  definition/location/uniqueness checks, full input coercion and literal type checking,
  all-variables-used, variable usage compatibility, fragment-must-be-used, and meta-field
  rules.
-/
namespace GraphQL

namespace Validation

-- Spec 5.5.2.1 Fragment Spread Target Defined: faithful fragment-name lookup helper for
-- modeled fragments.
def fragmentNamed? (fragments : List FragmentDefinition)
    (name : Name) : Option FragmentDefinition :=
  FragmentDefinition.find? fragments name

-- Spec 5.7 Directives: not faithful yet; all modeled directives are accepted without
-- checking definition, location, uniqueness, or argument validity.
def directivesValid (_directives : List DirectiveApplication) : Prop :=
  True

-- Spec 5.8.3 All Variable Uses Defined: partial helper for operation-level variable
-- lookup.
def variableDefinitionNamed? (variableDefinitions : List VariableDefinition)
    (name : Name) : Option VariableDefinition :=
  variableDefinitions.find? (fun variableDefinition => variableDefinition.name == name)

-- Spec 5.6.1 Values of Correct Type and 5.8.3 All Variable Uses Defined: partial; checks
-- expected input type and variable existence, but not literal coercion or variable usage
-- type compatibility.
def inputValueValid (schema : Schema) (variableDefinitions : List VariableDefinition)
    (value : InputValue) (expectedType : TypeRef) : Prop :=
  expectedType.validInput schema
    ∧ match value with
      | .variable variableName =>
          ∃ variableDefinition,
            variableDefinitionNamed? variableDefinitions variableName = some variableDefinition
      | _ => True

-- Spec 5.8.2 Variables Are Input Types: partial; also validates default values using the
-- simplified `inputValueValid`.
def variableDefinitionValid (schema : Schema)
    (variableDefinition : VariableDefinition) : Prop :=
  variableDefinition.typeRef.validInput schema
    ∧ match variableDefinition.defaultValue with
      | none => True
      | some defaultValue => inputValueValid schema [] defaultValue variableDefinition.typeRef

-- Spec 5.8.1 Variable Uniqueness and 5.8.2 Variables Are Input Types: partial; omits
-- all-variables-used and usage compatibility.
def variableDefinitionsValid (schema : Schema)
    (variableDefinitions : List VariableDefinition) : Prop :=
  (variableDefinitions.map VariableDefinition.name).Nodup
    ∧ ∀ variableDefinition, variableDefinition ∈ variableDefinitions ->
      variableDefinitionValid schema variableDefinition

-- Spec 5.4.1 Argument Names and 5.6.1 Values of Correct Type: partial; validates defined
-- argument names and simplified value validity.
def argumentValid (schema : Schema) (definitions : List InputValueDefinition)
    (variableDefinitions : List VariableDefinition) (argument : Argument) : Prop :=
  ∃ definition,
    Schema.lookupArgumentDefinition definitions argument.name = some definition
      ∧ inputValueValid schema variableDefinitions argument.value definition.inputType

def argumentNamed? (arguments : List Argument) (name : Name) : Option Argument :=
  arguments.find? (fun argument => argument.name == name)

-- Spec 5.4.3 Required Arguments: faithful for identifying non-null arguments without
-- defaults.
def argumentDefinitionRequired (definition : InputValueDefinition) : Prop :=
  match definition.inputType with
  | .nonNull _ => definition.defaultValue = none
  | _ => False

-- Spec 5.4.1-5.4.3 Argument validation: partial; handles names, uniqueness, required
-- arguments, and simplified value validity, but does not reject explicit null for
-- required arguments.
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

-- Spec 5.5.1.1 Fragment Name Uniqueness: faithful for the modeled fragment list.
def fragmentNamesNodup (fragments : List FragmentDefinition) : Prop :=
  (fragments.map FragmentDefinition.name).Nodup

-- Spec 5.5.2.1 Fragment Spread Target Defined: faithful for modeled spread-name lists.
def fragmentSpreadNamesResolve (fragments : List FragmentDefinition)
    (spreadNames : List Name) : Prop :=
  ∀ fragmentName, fragmentName ∈ spreadNames ->
    ∃ fragmentDefinition,
      fragmentNamed? fragments fragmentName = some fragmentDefinition

def selectionSetFragmentSpreadsResolve (fragments : List FragmentDefinition)
    (selectionSet : List Selection) : Prop :=
  fragmentSpreadNamesResolve fragments (SelectionSet.fragmentSpreadNames selectionSet)

def fragmentSpreadsResolve (fragments : List FragmentDefinition) : Prop :=
  ∀ fragment, fragment ∈ fragments ->
    fragmentSpreadNamesResolve fragments fragment.fragmentSpreadNames

-- Spec 5.5.2.2 `DetectFragmentCycles`: partial fuel-bounded acyclicity check over
-- fragment-name dependencies.
def fragmentDependencyAcyclicFrom (fragments : List FragmentDefinition) :
    Nat -> List Name -> Name -> Prop
  | 0, _path, _fragmentName => False
  | fuel + 1, path, fragmentName =>
      fragmentName ∉ path
        ∧ ∃ fragment,
          fragmentNamed? fragments fragmentName = some fragment
            ∧ ∀ dependency, dependency ∈ fragment.fragmentSpreadNames ->
              fragmentDependencyAcyclicFrom fragments fuel (fragmentName :: path) dependency

def fragmentDependenciesAcyclic (fragments : List FragmentDefinition) : Prop :=
  ∀ fragment, fragment ∈ fragments ->
    fragmentDependencyAcyclicFrom fragments (fragments.length + 1) [] fragment.name

def fragmentsValid (fragments : List FragmentDefinition) : Prop :=
  fragmentNamesNodup fragments
    ∧ fragmentSpreadsResolve fragments
    ∧ fragmentDependenciesAcyclic fragments

-- Spec 5.3 Field validation, 5.5 Fragment validation, and 5.7 Directive validation:
-- partial; combines modeled field lookup, arguments, leaf/composite subselection checks,
-- and fragment applicability.
mutual
  def selectionValid (schema : Schema) (fragments : List FragmentDefinition)
      (variableDefinitions : List VariableDefinition) (parentType : Name) : Selection -> Prop
    | .field _responseName fieldName arguments directives selectionSet =>
        directivesValid directives
          ∧ ∃ fieldDefinition,
            schema.lookupField parentType fieldName = some fieldDefinition
              ∧ argumentsValid schema fieldDefinition.arguments variableDefinitions arguments
              ∧ fieldSelectionSetValid schema fragments variableDefinitions
                fieldDefinition selectionSet
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

-- Spec 5.5.1 Fragment Declarations and 5.3.2 Field Selection Merging: partial; validates
-- object/interface/union type condition, non-empty selection set, nested selections, and
-- field merging.
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

-- Spec 5 Validation of executable operations: partial aggregate predicate over the
-- modeled single-operation representation.
def operationValid (schema : Schema) (operation : Operation) : Prop :=
  operation.rootType = schema.queryType
    ∧ schema.compositeType operation.rootType
    ∧ variableDefinitionsValid schema operation.variableDefinitions
    ∧ fragmentsValid operation.fragments
    ∧ operation.selectionSet ≠ []
    ∧ selectionSetFragmentSpreadsResolve operation.fragments operation.selectionSet
    ∧ selectionSetValid schema operation.fragments operation.variableDefinitions
      operation.rootType operation.selectionSet
    ∧ FieldMerge.selectionSetFieldsCanMerge schema operation.fragments operation.size
      operation.rootType operation.selectionSet
    ∧ ∀ fragment, fragment ∈ operation.fragments ->
      fragmentValid schema operation.fragments operation.variableDefinitions fragment

end Validation

end GraphQL
