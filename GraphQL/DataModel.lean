import GraphQL.Execution
import GraphQL.Validation

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

def pairwiseUniqueByEqBool {α : Type} (eqBool : α -> α -> Bool) :
    List α -> Prop
  | [] => True
  | key :: rest =>
      (∀ candidate, candidate ∈ rest -> eqBool key candidate = false)
        ∧ pairwiseUniqueByEqBool eqBool rest

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
    List (Name × InputValue) -> List (Name × InputValue) :=
  InputValue.insertObjectFieldSorted field

def sortInputFieldsByName : List (Name × InputValue) -> List (Name × InputValue) :=
  InputValue.sortObjectFieldsByName

def canonicalInputValue : InputValue -> InputValue :=
  InputValue.canonical

def canonicalInputValues : List InputValue -> List InputValue :=
  InputValue.canonicalValues

def canonicalInputFields : List (Name × InputValue) -> List (Name × InputValue) :=
  InputValue.canonicalObjectFields

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

def argumentsWellTyped (schema : Schema) (fieldDefinition : FieldDefinition)
    (field : FieldAccess) : Prop :=
  Validation.argumentsValid schema fieldDefinition.arguments [] field.arguments

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
      ∧ field.argumentsWellTyped schema fieldDefinition
      ∧ value.conformsToType schema fieldDefinition.outputType

def propertyKeys (node : ObjectNode) : List FieldAccess :=
  node.properties.map Prod.fst

def propertyKeysUnique (node : ObjectNode) : Prop :=
  pairwiseUniqueByEqBool FieldAccess.eqBool node.propertyKeys

def wellTyped (schema : Schema) (node : ObjectNode) : Prop :=
  schema.objectType node.typeName
    ∧ node.propertyKeysUnique
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

end ObjectEdge

structure FieldPathKey where
  sourcePath : ObjectPath
  field : FieldAccess
deriving Repr

namespace FieldPathKey

def eqBool (left right : FieldPathKey) : Bool :=
  ObjectPath.eqBool left.sourcePath right.sourcePath
    && FieldAccess.eqBool left.field right.field

end FieldPathKey

structure ListIndexKey where
  sourcePath : ObjectPath
  field : FieldAccess
  index : Nat
deriving Repr

namespace ListIndexKey

def eqBool (left right : ListIndexKey) : Bool :=
  ObjectPath.eqBool left.sourcePath right.sourcePath
    && FieldAccess.eqBool left.field right.field
    && (left.index == right.index)

end ListIndexKey

namespace ObjectEdge

def nonListKey? (edge : ObjectEdge) : Option FieldPathKey :=
  match edge.index? with
  | none => some { sourcePath := edge.sourcePath, field := edge.field }
  | some _ => none

def listIndexKey? (edge : ObjectEdge) : Option ListIndexKey :=
  match edge.index? with
  | none => none
  | some index =>
      some { sourcePath := edge.sourcePath, field := edge.field, index := index }

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

def insertEdgeByIndex (edge : ObjectEdge) : List ObjectEdge -> List ObjectEdge
  | [] => [edge]
  | candidate :: rest =>
      if edge.index?.getD 0 <= candidate.index?.getD 0 then
        edge :: candidate :: rest
      else
        candidate :: insertEdgeByIndex edge rest

def sortEdgesByIndex : List ObjectEdge -> List ObjectEdge
  | [] => []
  | edge :: rest => insertEdgeByIndex edge (sortEdgesByIndex rest)

def indexedMatchingEdgesUnsorted (store : Store) (sourcePath : ObjectPath)
    (field : FieldAccess) : List ObjectEdge :=
  (store.matchingEdges sourcePath field).filter (fun edge =>
    match edge.index? with
    | some _ => true
    | none => false)

def indexedMatchingEdges (store : Store) (sourcePath : ObjectPath)
    (field : FieldAccess) : List ObjectEdge :=
  sortEdgesByIndex (store.indexedMatchingEdgesUnsorted sourcePath field)

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

def nonListCompositeEdgeKeys (store : Store) : List FieldPathKey :=
  store.edges.filterMap ObjectEdge.nonListKey?

def nonListCompositeEdgesUnique (store : Store) : Prop :=
  pairwiseUniqueByEqBool FieldPathKey.eqBool store.nonListCompositeEdgeKeys

def listCompositeEdgeKeys (store : Store) : List ListIndexKey :=
  store.edges.filterMap ObjectEdge.listIndexKey?

def listCompositeEdgesUnique (store : Store) : Prop :=
  pairwiseUniqueByEqBool ListIndexKey.eqBool store.listCompositeEdgeKeys

def listCompositeEdgesDense (store : Store) : Prop :=
  ∀ edge, edge ∈ store.edges ->
    match edge.index? with
    | none => True
    | some index =>
        let edges := store.indexedMatchingEdges edge.sourcePath edge.field
        index < edges.length
          ∧ ∀ expected, expected < edges.length ->
            ∃ candidate, candidate ∈ edges ∧ candidate.index? = some expected

def nodePathsUnique (store : Store) : Prop :=
  pairwiseUniqueByEqBool ObjectPath.eqBool (store.allNodes.map ObjectNode.path)

def nodeCoveredByRootOrEdge (store : Store) (node : ObjectNode) : Prop :=
  ObjectPath.eqBool node.path store.root.path = true
    ∨ ∃ edge, edge ∈ store.edges ∧ ObjectPath.eqBool edge.targetPath node.path = true

def nodesCoveredByRootOrEdge (store : Store) : Prop :=
  ∀ node, node ∈ store.allNodes -> store.nodeCoveredByRootOrEdge node

def rootWellTyped (schema : Schema) (store : Store) : Prop :=
  store.root.path = []
    ∧ schema.typeIncludesObject schema.queryType store.root.typeName

def edgeWellTyped (schema : Schema) (store : Store)
    (edge : ObjectEdge) : Prop :=
  ∃ sourceNode fieldDefinition targetNode,
    store.lookupNode? edge.sourcePath = some sourceNode
      ∧ schema.lookupField sourceNode.typeName edge.field.name = some fieldDefinition
      ∧ schema.getPossibleTypes fieldDefinition.outputType.namedType ≠ []
      ∧ edge.field.argumentsWellTyped schema fieldDefinition
      ∧ (typeRefIsListLike fieldDefinition.outputType = true ↔ edge.index?.isSome)
      ∧ schema.typeIncludesObject fieldDefinition.outputType.namedType edge.targetType
      ∧ store.lookupNode? edge.targetPath = some targetNode
      ∧ targetNode.typeName = edge.targetType

def wellTyped (schema : Schema) (store : Store) : Prop :=
  store.rootWellTyped schema
    ∧ store.nodePathsUnique
    ∧ store.nodesCoveredByRootOrEdge
    ∧ (∀ node, node ∈ store.allNodes -> node.wellTyped schema)
    ∧ (∀ edge, edge ∈ store.edges -> store.edgeWellTyped schema edge)
    ∧ store.nonListCompositeEdgesUnique
    ∧ store.listCompositeEdgesUnique
    ∧ store.listCompositeEdgesDense

end Store

namespace Value

-- Spec-related bridge from proof-facing store values to execution resolver values.
def toExecutionValue : Value -> Execution.Value ObjectPath
  | .null => .null
  | .scalar value => .scalar value
  | .object typeName identity => .object typeName identity
  | .list values => .list (values.map toExecutionValue)

end Value

namespace Store

def rootExecutionValue (store : Store) : Execution.Value ObjectPath :=
  .object store.root.typeName store.root.path

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
    (operation : Operation) : Execution.Response :=
  Execution.executeQuery schema (store.resolvers schema) variableValues
    operation store.rootExecutionValue

-- Explicit-depth store-backed execution used by semantic equivalence theorems.
def executeOperationAtDepth (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues) (operation : Operation)
    (depth : Nat) : Execution.Response :=
  Execution.executeQueryAtDepth schema (store.resolvers schema) variableValues
    operation depth store.rootExecutionValue

-- Spec-related operation equivalence over all well-typed graph stores.
def operationsEquivalentOnData (schema : Schema)
    (left right : Operation) : Prop :=
  ∀ store variableValues depth,
    store.wellTyped schema ->
      executeOperationAtDepth schema store variableValues left depth
        = executeOperationAtDepth schema store variableValues right depth

end DataModel

end GraphQL
