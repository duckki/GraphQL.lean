import GraphQL.FieldMerge

/-!
Spec reference: GraphQL September 2025.
- 5.2 Operations, 5.3 Fields, 5.4 Arguments, 5.5 Fragments, 5.6 Values, 5.7 Directives,
  and 5.8 Variables: this file states operation validity as a proposition over the modeled
  schema and operation syntax.
- Fidelity note: the model is intentionally partial. It omits document-level
  multi-operation rules, mutation/subscription rules, custom directive definitions, full
  input coercion and literal type checking, all-variables-used, general variable usage
  compatibility, fragment-must-be-used, and meta-field rules.
-/
namespace GraphQL

namespace Validation

-- Spec 5.5.2.1 Fragment Spread Target Defined: faithful fragment-name lookup helper for
-- modeled fragments.
def getFragmentDefinition? (fragments : List FragmentDefinition)
    (name : Name) : Option FragmentDefinition :=
  FragmentDefinition.find? fragments name

-- Spec 5.8.3 All Variable Uses Defined: partial helper for operation-level variable
-- lookup.
def getVariableDefinition? (variableDefinitions : List VariableDefinition)
    (name : Name) : Option VariableDefinition :=
  variableDefinitions.find? (fun variableDefinition => variableDefinition.name == name)

def constInputValueNonNull : ConstInputValue -> Prop
  | .null => False
  | _ => True

def inputValueNonNull : InputValue -> Prop
  | .null => False
  | _ => True

def getInputObjectField? (fields : List (Name × InputValue))
    (name : Name) : Option InputValue :=
  match fields with
  | [] => none
  | (fieldName, value) :: rest =>
      if fieldName = name then some value else getInputObjectField? rest name

-- Spec 5.4.3 / 5.6.4 required input entries: non-null type with no default.
def isRequiredInputValueDefinition (definition : InputValueDefinition) : Prop :=
  match definition.inputType with
  | .nonNull _ => definition.defaultValue = none
  | _ => False

mutual
  -- Spec 5.6.1 Values of Correct Type, 5.6.2-5.6.4 input object rules, and 5.8.3
  -- variable existence. Literal coercion remains deliberately shallow, but input-object
  -- structure is checked recursively.
  def valueIsCorrectTypeWithFuel (schema : Schema)
      (variableDefinitions : List VariableDefinition) :
      Nat -> InputValue -> TypeRef -> Prop
    | 0, _value, _expectedType => False
    | fuel + 1, value, expectedType =>
        expectedType.isInputType schema
          ∧ match value, expectedType with
            | .variable variableName, _ =>
                ∃ variableDefinition,
                  getVariableDefinition? variableDefinitions variableName =
                    some variableDefinition
            | .null, .nonNull _ => False
            | .null, _ => True
            | _, .nonNull inner =>
                valueIsCorrectTypeWithFuel schema variableDefinitions fuel value inner
            | .list values, .list inner =>
                ∀ item, item ∈ values ->
                  valueIsCorrectTypeWithFuel schema variableDefinitions fuel item inner
            | .list _values, _ => False
            | .object fields, .named typeName =>
                ∃ inputObject,
                  schema.lookupInputObject typeName = some inputObject
                    ∧ inputObjectFieldsValidWithFuel schema variableDefinitions fuel
                      inputObject.inputFields fields
            | .object fields, .list inner =>
                inputObjectAsListItemValidWithFuel schema variableDefinitions fuel
                  fields inner
            | _value, .list inner =>
                valueIsCorrectTypeWithFuel schema variableDefinitions fuel value inner
            | _value, _expectedType => True

  def inputObjectFieldsValidWithFuel (schema : Schema)
      (variableDefinitions : List VariableDefinition) :
      Nat -> List InputValueDefinition -> List (Name × InputValue) -> Prop
    | 0, _definitions, _fields => False
    | fuel + 1, definitions, fields =>
        (fields.map Prod.fst).Nodup
          ∧ (∀ name value, (name, value) ∈ fields ->
            ∃ definition,
              Schema.lookupArgumentDefinition definitions name = some definition
                ∧ valueIsCorrectTypeWithFuel schema variableDefinitions fuel
                  value definition.inputType)
          ∧ (∀ definition, definition ∈ definitions ->
            isRequiredInputValueDefinition definition ->
              ∃ value,
                getInputObjectField? fields definition.name = some value
                  ∧ inputValueNonNull value)

  def inputObjectAsListItemValidWithFuel (schema : Schema)
      (variableDefinitions : List VariableDefinition) :
      Nat -> List (Name × InputValue) -> TypeRef -> Prop
    | 0, _fields, _inner => False
    | fuel + 1, fields, inner =>
        valueIsCorrectTypeWithFuel schema variableDefinitions fuel
          (.object fields) inner
end

def valueIsCorrectType (schema : Schema) (variableDefinitions : List VariableDefinition)
    (value : InputValue) (expectedType : TypeRef) : Prop :=
  valueIsCorrectTypeWithFuel schema variableDefinitions
    (value.size + expectedType.size + 1) value expectedType

-- Spec 2.10 `Value Const` / 5.6.1 defaults: defaults are structurally constant and use
-- the same scoped validation as runtime input values.
def constValueIsCorrectType (schema : Schema)
    (value : ConstInputValue) (expectedType : TypeRef) : Prop :=
  valueIsCorrectType schema [] value.toInputValue expectedType

def booleanNonNullType : TypeRef :=
  .nonNull (.named "Boolean")

def variableUsableAtNonNullBoolean (schema : Schema)
    (variableDefinition : VariableDefinition) : Prop :=
  variableDefinition.typeRef.isInputType schema
    ∧ (variableDefinition.typeRef = booleanNonNullType
      ∨ (variableDefinition.typeRef = .named "Boolean"
        ∧ ∃ defaultValue,
          variableDefinition.defaultValue = some defaultValue
            ∧ constInputValueNonNull defaultValue))

def directiveIfArgumentValid (schema : Schema)
    (variableDefinitions : List VariableDefinition) : InputValue -> Prop
  | .boolean _ => True
  | .variable variableName =>
      ∃ variableDefinition,
        getVariableDefinition? variableDefinitions variableName = some variableDefinition
          ∧ variableUsableAtNonNullBoolean schema variableDefinition
  | _ => False

def directiveName : DirectiveApplication -> Name
  | .skip _ => "skip"
  | .include _ => "include"

def directiveValid (schema : Schema)
    (variableDefinitions : List VariableDefinition) : DirectiveApplication -> Prop
  | .skip ifArgument =>
      directiveIfArgumentValid schema variableDefinitions ifArgument
  | .include ifArgument =>
      directiveIfArgumentValid schema variableDefinitions ifArgument

-- Spec 5.7 Directives for the modeled executable subset: `@skip` and `@include` are
-- defined at selection locations, are non-repeatable, and require `if: Boolean!`.
def directivesValid (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (directives : List DirectiveApplication) : Prop :=
  (directives.map directiveName).Nodup
    ∧ ∀ directive, directive ∈ directives ->
      directiveValid schema variableDefinitions directive

-- Spec 5.8.2 Variables Are Input Types: partial; also validates default values using the
-- simplified `valueIsCorrectType`.
def variableDefinitionValid (schema : Schema)
    (variableDefinition : VariableDefinition) : Prop :=
  variableDefinition.typeRef.isInputType schema
    ∧ match variableDefinition.defaultValue with
      | none => True
      | some defaultValue =>
          constValueIsCorrectType schema defaultValue variableDefinition.typeRef

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
      ∧ valueIsCorrectType schema variableDefinitions argument.value definition.inputType

def getArgument? (arguments : List Argument) (name : Name) : Option Argument :=
  arguments.find? (fun argument => argument.name == name)

-- Spec 5.4.3 Required Arguments: faithful for identifying non-null arguments without
-- defaults.
def isRequiredArgument (definition : InputValueDefinition) : Prop :=
  isRequiredInputValueDefinition definition

-- Spec 5.4.1-5.4.3 Argument validation: partial; handles names, uniqueness, required
-- arguments, and simplified value validity.
def argumentsValid (schema : Schema) (definitions : List InputValueDefinition)
    (variableDefinitions : List VariableDefinition) (arguments : List Argument) : Prop :=
  (arguments.map Argument.name).Nodup
    ∧ (∀ argument, argument ∈ arguments ->
      argumentValid schema definitions variableDefinitions argument)
    ∧ (∀ definition, definition ∈ definitions ->
      isRequiredArgument definition ->
        ∃ argument,
          getArgument? arguments definition.name = some argument
            ∧ inputValueNonNull argument.value)

def fragmentsSize (fragments : List FragmentDefinition) : Nat :=
  fragments.foldl (fun total fragment => total + fragment.size) 0

-- Spec 5.5.1.1 Fragment Name Uniqueness: faithful for the modeled fragment list.
def fragmentNamesAreUnique (fragments : List FragmentDefinition) : Prop :=
  (fragments.map FragmentDefinition.name).Nodup

-- Spec 5.5.2.1 Fragment Spread Target Defined: faithful for modeled spread-name lists.
def fragmentSpreadTargetsDefined (fragments : List FragmentDefinition)
    (spreadNames : List Name) : Prop :=
  ∀ fragmentName, fragmentName ∈ spreadNames ->
    ∃ fragmentDefinition,
      getFragmentDefinition? fragments fragmentName = some fragmentDefinition

-- Spec 5.5.2.1 Fragment Spread Target Defined: operation selection-set wrapper.
def selectionSetFragmentSpreadTargetsDefined (fragments : List FragmentDefinition)
    (selectionSet : List Selection) : Prop :=
  fragmentSpreadTargetsDefined fragments (SelectionSet.fragmentSpreadNames selectionSet)

-- Spec 5.5.2.1 Fragment Spread Target Defined: fragment-definition aggregate wrapper.
def fragmentDefinitionSpreadTargetsDefined (fragments : List FragmentDefinition) : Prop :=
  ∀ fragment, fragment ∈ fragments ->
    fragmentSpreadTargetsDefined fragments fragment.fragmentSpreadNames

-- Spec 5.5.2.2 `DetectFragmentCycles`: partial fuel-bounded acyclicity check over
-- fragment-name dependencies.
def fragmentDependencyAcyclicFrom (fragments : List FragmentDefinition) :
    Nat -> List Name -> Name -> Prop
  | 0, _path, _fragmentName => False
  | fuel + 1, path, fragmentName =>
      fragmentName ∉ path
        ∧ ∃ fragment,
          getFragmentDefinition? fragments fragmentName = some fragment
            ∧ ∀ dependency, dependency ∈ fragment.fragmentSpreadNames ->
              fragmentDependencyAcyclicFrom fragments fuel (fragmentName :: path) dependency

-- Spec 5.5.2.2 Fragment Spreads Must Not Form Cycles: aggregate acyclicity predicate.
def fragmentDependenciesAcyclic (fragments : List FragmentDefinition) : Prop :=
  ∀ fragment, fragment ∈ fragments ->
    fragmentDependencyAcyclicFrom fragments (fragments.length + 1) [] fragment.name

-- Spec 5.5 Fragment validation: aggregate over the modeled fragment-declaration rules.
def fragmentsValid (fragments : List FragmentDefinition) : Prop :=
  fragmentNamesAreUnique fragments
    ∧ fragmentDefinitionSpreadTargetsDefined fragments
    ∧ fragmentDependenciesAcyclic fragments

-- Spec 5.3 Field validation, 5.5 Fragment validation, and 5.7 Directive validation:
-- partial; combines modeled field lookup, arguments, leaf/composite subselection checks,
-- and fragment applicability.
mutual
  def selectionValid (schema : Schema) (fragments : List FragmentDefinition)
      (variableDefinitions : List VariableDefinition) (parentType : Name) : Selection -> Prop
    | .field _responseName fieldName arguments directives selectionSet =>
        directivesValid schema variableDefinitions directives
          ∧ ∃ fieldDefinition,
            schema.lookupField parentType fieldName = some fieldDefinition
              ∧ argumentsValid schema fieldDefinition.arguments variableDefinitions arguments
              ∧ fieldSelectionSetValid schema fragments variableDefinitions
                fieldDefinition selectionSet
    | .fragmentSpread fragmentName directives =>
        directivesValid schema variableDefinitions directives
          ∧ ∃ fragmentDefinition,
            getFragmentDefinition? fragments fragmentName = some fragmentDefinition
              ∧ schema.typesOverlap parentType fragmentDefinition.typeCondition
    | .inlineFragment none directives selectionSet =>
        directivesValid schema variableDefinitions directives
          ∧ selectionSet ≠ []
          ∧ selectionSetValid schema fragments variableDefinitions parentType selectionSet
    | .inlineFragment (some typeCondition) directives selectionSet =>
        directivesValid schema variableDefinitions directives
          ∧ schema.isCompositeType typeCondition
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
    fieldDefinition.outputType.isOutputType schema
      ∧ ((schema.isLeafType returnType ∧ selectionSet = [])
      ∨ (schema.isCompositeType returnType
        ∧ selectionSet ≠ []
        ∧ selectionSetValid schema fragments variableDefinitions returnType selectionSet))
end

-- Spec 5.5.1 Fragment Declarations and 5.3.2 Field Selection Merging: partial; validates
-- object/interface/union type condition, non-empty selection set, nested selections, and
-- field merging.
def fragmentDefinitionValid (schema : Schema) (fragments : List FragmentDefinition)
    (variableDefinitions : List VariableDefinition)
    (fragment : FragmentDefinition) : Prop :=
  schema.isCompositeType fragment.typeCondition
    ∧ fragment.selectionSet ≠ []
    ∧ selectionSetValid schema fragments variableDefinitions
      fragment.typeCondition fragment.selectionSet
    ∧ FieldMerge.fieldsInSetCanMerge schema fragments
      (fragment.size + fragmentsSize fragments)
      fragment.typeCondition fragment.selectionSet

-- Spec 5.2 Operation validation plus referenced executable validation rules: partial
-- aggregate predicate over the modeled single-operation representation.
def operationDefinitionValid (schema : Schema) (operation : Operation) : Prop :=
  operation.rootType = schema.queryType
    ∧ schema.isCompositeType operation.rootType
    ∧ variableDefinitionsValid schema operation.variableDefinitions
    ∧ fragmentsValid operation.fragments
    ∧ operation.selectionSet ≠ []
    ∧ selectionSetFragmentSpreadTargetsDefined operation.fragments operation.selectionSet
    ∧ selectionSetValid schema operation.fragments operation.variableDefinitions
      operation.rootType operation.selectionSet
    ∧ FieldMerge.fieldsInSetCanMerge schema operation.fragments operation.size
      operation.rootType operation.selectionSet
    ∧ ∀ fragment, fragment ∈ operation.fragments ->
      fragmentDefinitionValid schema operation.fragments operation.variableDefinitions fragment

end Validation

end GraphQL
