import GraphQL.Execution

/-!
Spec reference: GraphQL September 2025.
- 6 Execution and 7 Response: this module gives an extensional graph-backed data model
  for the intentionally scoped execution fragment: query-like operations,
  already-coerced arguments/variables, built-in `@skip`/`@include`, no introspection,
  no mutation, and no subscription.
- The model represents typed object nodes keyed by field-access paths. Scalar facts live
  as node properties, object relationships live as labeled edges, and the model can be
  converted into the existing resolver interface.
- Fidelity note: scalar coercion, enum coercion, input coercion, result coercion,
  execution errors, null bubbling, and serialization are assumed out of scope here.
-/
namespace GraphQL

namespace DataModel

structure FieldAccess where
  name : Name
  arguments : List Argument := []
deriving Repr

inductive PathStep where
  | field : FieldAccess -> PathStep
  | index : Nat -> PathStep
deriving Repr

abbrev ObjectPath := List PathStep

namespace FieldAccess

def insertInputFieldSorted
    (field : Name × InputValue) :
    List (Name × InputValue) -> List (Name × InputValue)
  | [] => [field]
  | candidate :: rest =>
      if field.1 <= candidate.1 then
        field :: candidate :: rest
      else
        candidate :: insertInputFieldSorted field rest

def sortInputFieldsByName : List (Name × InputValue) -> List (Name × InputValue)
  | [] => []
  | field :: rest =>
      insertInputFieldSorted field (sortInputFieldsByName rest)

mutual
  def canonicalInputValue : InputValue -> InputValue
    | .null => .null
    | .int value => .int value
    | .float value => .float value
    | .string value => .string value
    | .boolean value => .boolean value
    | .enum value => .enum value
    | .variable name => .variable name
    | .list values => .list (canonicalInputValues values)
    | .object fields =>
        .object (sortInputFieldsByName (canonicalInputFields fields))

  def canonicalInputValues : List InputValue -> List InputValue
    | [] => []
    | value :: rest =>
        canonicalInputValue value :: canonicalInputValues rest

  def canonicalInputFields :
      List (Name × InputValue) -> List (Name × InputValue)
    | [] => []
    | (name, value) :: rest =>
        (name, canonicalInputValue value) :: canonicalInputFields rest
end

mutual
  def structuralInputValueEqBool : InputValue -> InputValue -> Bool
    | .null, .null => true
    | .int left, .int right => left == right
    | .float left, .float right => left == right
    | .string left, .string right => left == right
    | .boolean left, .boolean right => left == right
    | .enum left, .enum right => left == right
    | .variable left, .variable right => left == right
    | .list left, .list right => structuralInputValuesEqBool left right
    | .object left, .object right => structuralInputFieldsEqBool left right
    | _left, _right => false

  def structuralInputValuesEqBool :
      List InputValue -> List InputValue -> Bool
    | [], [] => true
    | left :: leftRest, right :: rightRest =>
        structuralInputValueEqBool left right
          && structuralInputValuesEqBool leftRest rightRest
    | _left, _right => false

  def structuralInputFieldsEqBool :
      List (Name × InputValue) -> List (Name × InputValue) -> Bool
    | [], [] => true
    | (leftName, leftValue) :: leftRest,
        (rightName, rightValue) :: rightRest =>
        (leftName == rightName)
          && structuralInputValueEqBool leftValue rightValue
          && structuralInputFieldsEqBool leftRest rightRest
    | _left, _right => false
end

def inputValueEqBool (left right : InputValue) : Bool :=
  structuralInputValueEqBool
    (canonicalInputValue left) (canonicalInputValue right)

def canonicalArgument (argument : Argument) : Argument :=
  { argument with value := canonicalInputValue argument.value }

def argumentEqBool (left right : Argument) : Bool :=
  (left.name == right.name)
    && structuralInputValueEqBool
      (canonicalInputValue left.value) (canonicalInputValue right.value)

def insertArgumentSorted (argument : Argument) : List Argument -> List Argument
  | [] => [argument]
  | candidate :: rest =>
      if argument.name <= candidate.name then
        argument :: candidate :: rest
      else
        candidate :: insertArgumentSorted argument rest

def sortArgumentsByName : List Argument -> List Argument
  | [] => []
  | argument :: rest =>
      insertArgumentSorted argument (sortArgumentsByName rest)

def canonicalArguments : List Argument -> List Argument
  | [] => []
  | argument :: rest =>
      canonicalArgument argument :: canonicalArguments rest

def argumentsEqBoolOrdered : List Argument -> List Argument -> Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      argumentEqBool left right && argumentsEqBoolOrdered leftRest rightRest
  | _left, _right => false

def argumentsEqBool (left right : List Argument) : Bool :=
  argumentsEqBoolOrdered
    (sortArgumentsByName (canonicalArguments left))
    (sortArgumentsByName (canonicalArguments right))

def canonical (field : FieldAccess) : FieldAccess :=
  { field with arguments := sortArgumentsByName (canonicalArguments field.arguments) }

def eqBool (left right : FieldAccess) : Bool :=
  (left.name == right.name) && argumentsEqBool left.arguments right.arguments

def childPath (sourcePath : ObjectPath) (field : FieldAccess) : ObjectPath :=
  sourcePath ++ [.field field.canonical]

def childListElementPath
    (sourcePath : ObjectPath) (field : FieldAccess) (index : Nat) :
    ObjectPath :=
  sourcePath ++ [.field field.canonical, .index index]

end FieldAccess

namespace PathStep

def eqBool : PathStep -> PathStep -> Bool
  | .field left, .field right => FieldAccess.eqBool left right
  | .index left, .index right => left == right
  | _, _ => false

end PathStep

namespace ObjectPath

def eqBool : ObjectPath -> ObjectPath -> Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      PathStep.eqBool left right && eqBool leftRest rightRest
  | _, _ => false

end ObjectPath

-- Host result values before GraphQL response serialization, retaining runtime object type.
inductive Value where
  | null
  | scalar (value : String)
  | object (typeName : Name) (identity : ObjectPath)
  | list (values : List Value)
deriving Repr

namespace Value

-- Assumption boundary for the scoped model: result values are already type-conformant.
def conformsToType (schema : Schema) : Value -> TypeRef -> Prop
  | .null, .nonNull _inner => False
  | .null, _typeRef => True
  | .scalar _value, .named typeName => schema.isLeafType typeName
  | .scalar value, .nonNull inner => conformsToType schema (.scalar value) inner
  | .scalar _value, .list _inner => False
  | .object objectType _identity, .named typeName =>
      schema.typeIncludesObject typeName objectType
  | .object objectType identity, .nonNull inner =>
      conformsToType schema (.object objectType identity) inner
  | .object _objectType _identity, .list _inner => False
  | .list values, .list inner =>
      ∀ value, value ∈ values -> conformsToType schema value inner
  | .list values, .nonNull inner => conformsToType schema (.list values) inner
  | .list _values, .named _typeName => False

end Value

-- Node-local property values. Object relationships are represented by graph edges.
inductive PropertyValue where
  | null
  | scalar (value : String)
  | list (values : List PropertyValue)
deriving Repr

namespace PropertyValue

def toValue : PropertyValue -> Value
  | .null => .null
  | .scalar value => .scalar value
  | .list values => .list (values.map toValue)

def conformsToType (schema : Schema) (value : PropertyValue)
    (typeRef : TypeRef) : Prop :=
  value.toValue.conformsToType schema typeRef

end PropertyValue

def typeRefIsListLike : TypeRef -> Bool
  | .list _inner => true
  | .nonNull inner => typeRefIsListLike inner
  | .named _typeName => false

-- Graph node for one typed runtime object.
structure ObjectNode where
  typeName : Name
  path : ObjectPath
  properties : List (FieldAccess × PropertyValue) := []
deriving Repr

namespace ObjectNode

def lookupPropertyIn? (field : FieldAccess) :
    List (FieldAccess × PropertyValue) -> Option PropertyValue
  | [] => none
  | (candidate, value) :: rest =>
      if FieldAccess.eqBool candidate field then
        some value
      else
        lookupPropertyIn? field rest

def lookupProperty? (node : ObjectNode) (field : FieldAccess) :
    Option PropertyValue :=
  lookupPropertyIn? field node.properties

def propertyFactWellTyped (schema : Schema) (node : ObjectNode)
    (field : FieldAccess) (value : PropertyValue) : Prop :=
  ∃ fieldDefinition,
    schema.lookupField node.typeName field.name = some fieldDefinition
      ∧ schema.getPossibleTypes fieldDefinition.outputType.namedType = []
      ∧ value.conformsToType schema fieldDefinition.outputType

def wellTyped (schema : Schema) (node : ObjectNode) : Prop :=
  schema.objectType node.typeName
    ∧ ∀ property, property ∈ node.properties ->
      propertyFactWellTyped schema node property.fst property.snd

end ObjectNode

-- Graph edge for one object-valued field access.
structure ObjectEdge where
  sourcePath : ObjectPath
  field : FieldAccess
  index? : Option Nat := none
  targetType : Name
deriving Repr

namespace ObjectEdge

def targetPath (edge : ObjectEdge) : ObjectPath :=
  match edge.index? with
  | none => FieldAccess.childPath edge.sourcePath edge.field
  | some index => FieldAccess.childListElementPath edge.sourcePath edge.field index

def matchesField (sourcePath : ObjectPath) (field : FieldAccess)
    (edge : ObjectEdge) : Bool :=
  ObjectPath.eqBool edge.sourcePath sourcePath
    && FieldAccess.eqBool edge.field field

def nonListKey? (edge : ObjectEdge) : Option (ObjectPath × FieldAccess) :=
  match edge.index? with
  | none => some (edge.sourcePath, edge.field)
  | some _ => none

end ObjectEdge

-- Finite graph store used to instantiate the execution resolver API.
structure Store where
  root : ObjectNode
  nodes : List ObjectNode := []
  edges : List ObjectEdge := []
deriving Repr

namespace Store

def allNodes (store : Store) : List ObjectNode :=
  store.root :: store.nodes

def lookupNodeIn? (path : ObjectPath) :
    List ObjectNode -> Option ObjectNode
  | [] => none
  | node :: rest =>
      if ObjectPath.eqBool node.path path then
        some node
      else
        lookupNodeIn? path rest

def lookupNode? (store : Store) (path : ObjectPath) : Option ObjectNode :=
  lookupNodeIn? path store.allNodes

def matchingEdges (store : Store) (sourcePath : ObjectPath)
    (field : FieldAccess) : List ObjectEdge :=
  store.edges.filter (fun edge => edge.matchesField sourcePath field)

def firstMatchingEdge? (store : Store) (sourcePath : ObjectPath)
    (field : FieldAccess) (index? : Option Nat) : Option ObjectEdge :=
  store.edges.find? (fun edge =>
    edge.matchesField sourcePath field && edge.index? == index?)

def indexedMatchingEdges (store : Store) (sourcePath : ObjectPath)
    (field : FieldAccess) : List ObjectEdge :=
  (store.matchingEdges sourcePath field).filter (fun edge =>
    match edge.index? with
    | some _ => true
    | none => false)

def fieldAccess (fieldName : Name) (arguments : List Argument) : FieldAccess :=
  { name := fieldName, arguments := arguments }

def resolveValue (store : Store) (schema : Schema)
    (fieldName : Name) (arguments : List Argument) : Value -> Value
  | .object runtimeType sourcePath =>
      match store.lookupNode? sourcePath with
      | none => .null
      | some node =>
          if node.typeName == runtimeType then
            match schema.lookupField runtimeType fieldName with
            | none => .null
            | some fieldDefinition =>
                let field := fieldAccess fieldName arguments
                if schema.getPossibleTypes fieldDefinition.outputType.namedType = [] then
                  match node.lookupProperty? field with
                  | none => .null
                  | some property => property.toValue
                else if typeRefIsListLike fieldDefinition.outputType then
                  .list ((store.indexedMatchingEdges sourcePath field).map
                    (fun edge => .object edge.targetType edge.targetPath))
                else
                  match store.firstMatchingEdge? sourcePath field none with
                  | none => .null
                  | some edge => .object edge.targetType edge.targetPath
          else
            .null
  | _ => .null

def nonListCompositeEdgeKeys (store : Store) :
    List (ObjectPath × FieldAccess) :=
  store.edges.filterMap ObjectEdge.nonListKey?

def nonListCompositeEdgesUnique (store : Store) : Prop :=
  store.nonListCompositeEdgeKeys.Nodup

def edgeWellTyped (schema : Schema) (store : Store)
    (edge : ObjectEdge) : Prop :=
  ∃ sourceNode fieldDefinition targetNode,
    store.lookupNode? edge.sourcePath = some sourceNode
      ∧ schema.lookupField sourceNode.typeName edge.field.name = some fieldDefinition
      ∧ schema.getPossibleTypes fieldDefinition.outputType.namedType ≠ []
      ∧ (typeRefIsListLike fieldDefinition.outputType = true ↔ edge.index?.isSome)
      ∧ schema.typeIncludesObject fieldDefinition.outputType.namedType edge.targetType
      ∧ store.lookupNode? edge.targetPath = some targetNode
      ∧ targetNode.typeName = edge.targetType

def wellTyped (schema : Schema) (store : Store) : Prop :=
  store.root.path = []
    ∧ (store.allNodes.map ObjectNode.path).Nodup
    ∧ (∀ node, node ∈ store.allNodes -> node.wellTyped schema)
    ∧ (∀ edge, edge ∈ store.edges -> store.edgeWellTyped schema edge)
    ∧ store.nonListCompositeEdgesUnique

end Store

-- Query root object identity for store-backed execution.
structure Root where
  typeName : Name
  identity : ObjectPath := []
deriving Repr

namespace Root

def wellTyped (schema : Schema) (root : Root) : Prop :=
  root.identity = []
    ∧ schema.typeIncludesObject schema.queryType root.typeName

def toExecutionValue (root : Root) : Execution.Value ObjectPath :=
  .object root.typeName root.identity

end Root

namespace Value

-- Spec-related bridge from proof-facing store values to execution resolver values.
def toExecutionValue : Value -> Execution.Value ObjectPath
  | .null => .null
  | .scalar value => .scalar value
  | .object typeName identity => .object typeName identity
  | .list values => .list (values.map toExecutionValue)

end Value

namespace Store

def resolve (store : Store) (schema : Schema) (fieldName : Name)
    (arguments : List Argument) (source : Execution.Value ObjectPath) :
    Execution.Value ObjectPath :=
  match source with
  | .object runtimeType identity =>
      (store.resolveValue schema fieldName arguments
        (.object runtimeType identity)).toExecutionValue
  | _ => .null

def resolvers (store : Store) (schema : Schema) : Execution.Resolvers ObjectPath :=
  { resolve := fun _parentType fieldName arguments source =>
      store.resolve schema fieldName arguments source }

end Store

-- Spec 6.2.1 `ExecuteQuery` over raw modeled operations and store-backed resolvers.
def executeOperation (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (root : Root) : Execution.Response :=
  Execution.executeQuery schema (store.resolvers schema) variableValues
    operation root.toExecutionValue

-- Explicit-depth store-backed execution used by semantic equivalence theorems.
def executeOperationAtDepth (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (depth : Nat) (root : Root) : Execution.Response :=
  Execution.executeQueryAtDepth schema (store.resolvers schema) variableValues
    operation depth root.toExecutionValue

-- Spec-related operation equivalence over all well-typed store/root inputs.
def operationsEquivalentOnData (schema : Schema)
    (left right : Operation) : Prop :=
  ∀ store variableValues depth root,
    store.wellTyped schema ->
      root.wellTyped schema ->
        executeOperationAtDepth schema store variableValues left depth root
          = executeOperationAtDepth schema store variableValues right depth root

end DataModel

end GraphQL
