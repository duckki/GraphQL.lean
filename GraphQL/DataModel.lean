import GraphQL.Execution
import GraphQL.DataModel.ObjectRef
import GraphQL.Validation

/-! GraphQL data model for store-backed resolvers

This module models the server-side graph accessed through resolvers. Runtime objects are
typed nodes; scalar facts are node properties, and object relationships are labeled edges.
The model assumes scalar/input/result coercion, execution errors, null bubbling, and
serialization are outside the current scoped fragment.
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

-- Assumption boundary for the scoped model: result values are already type-conformant.
def valueConformsToType (schema : Schema) :
    Execution.Value ObjectRef -> TypeRef -> Prop
  | .null, .nonNull _inner => False
  | .null, _typeRef => True
  | .scalar _value, .named typeName => schema.isLeafType typeName
  | .scalar value, .nonNull inner =>
      valueConformsToType schema (.scalar value) inner
  | .scalar _value, .list _inner => False
  | .object objectType _ref, .named typeName =>
      schema.typeIncludesObject typeName objectType
  | .object objectType ref, .nonNull inner =>
      valueConformsToType schema (.object objectType ref) inner
  | .object _objectType _ref, .list _inner => False
  | .list values, .list inner =>
      ∀ value, value ∈ values -> valueConformsToType schema value inner
  | .list values, .nonNull inner =>
      valueConformsToType schema (.list values) inner
  | .list _values, .named _typeName => False

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

end FieldAccess

-- Node-local property values. Object relationships are represented by graph edges.
inductive PropertyValue where
  | null
  | scalar (value : String)
  | list (values : List PropertyValue)
deriving Repr

namespace PropertyValue

def toValue : PropertyValue -> Execution.Value ObjectRef
  | .null => .null
  | .scalar value => .scalar value
  | .list values => .list (values.map toValue)

def conformsToType (schema : Schema) (value : PropertyValue)
    (typeRef : TypeRef) : Prop :=
  valueConformsToType schema value.toValue typeRef

end PropertyValue

def typeRefIsListLike : TypeRef -> Bool
  | .list _inner => true
  | .nonNull inner => typeRefIsListLike inner
  | .named _typeName => false

-- Graph node for one typed runtime object.
structure ObjectNode where
  id : ObjectId
  typeName : Name
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
  sourceId : ObjectId
  field : FieldAccess
  index? : Option Nat := none
  targetId : ObjectId
  targetType : Name
deriving Repr

namespace ObjectEdge

def matchesField (sourceId : ObjectId) (field : FieldAccess)
    (edge : ObjectEdge) : Bool :=
  (edge.sourceId == sourceId)
    && FieldAccess.eqBool edge.field field

end ObjectEdge

structure FieldAccessKey where
  sourceId : ObjectId
  field : FieldAccess
deriving Repr

namespace FieldAccessKey

def eqBool (left right : FieldAccessKey) : Bool :=
  (left.sourceId == right.sourceId)
    && FieldAccess.eqBool left.field right.field

end FieldAccessKey

structure ListIndexKey where
  sourceId : ObjectId
  field : FieldAccess
  index : Nat
deriving Repr

namespace ListIndexKey

def eqBool (left right : ListIndexKey) : Bool :=
  (left.sourceId == right.sourceId)
    && FieldAccess.eqBool left.field right.field
    && (left.index == right.index)

end ListIndexKey

namespace ObjectEdge

def nonListKey? (edge : ObjectEdge) : Option FieldAccessKey :=
  match edge.index? with
  | none => some { sourceId := edge.sourceId, field := edge.field }
  | some _ => none

def listIndexKey? (edge : ObjectEdge) : Option ListIndexKey :=
  match edge.index? with
  | none => none
  | some index =>
      some { sourceId := edge.sourceId, field := edge.field, index := index }

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

def lookupNode? (store : Store) (id : ObjectId) : Option ObjectNode :=
  store.allNodes.find? (fun node => node.id == id)

def firstNodeWithType? (store : Store) (runtimeType : Name) : Option ObjectNode :=
  store.allNodes.find? (fun node => node.typeName == runtimeType)

def matchingEdges (store : Store) (sourceId : ObjectId)
    (field : FieldAccess) : List ObjectEdge :=
  store.edges.filter (fun edge => edge.matchesField sourceId field)

def firstMatchingEdge? (store : Store) (sourceId : ObjectId)
    (field : FieldAccess) (index? : Option Nat) : Option ObjectEdge :=
  store.edges.find? (fun edge =>
    edge.matchesField sourceId field && edge.index? == index?)

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

def indexedMatchingEdgesUnsorted (store : Store) (sourceId : ObjectId)
    (field : FieldAccess) : List ObjectEdge :=
  (store.matchingEdges sourceId field).filter (fun edge =>
    match edge.index? with
    | some _ => true
    | none => false)

def indexedMatchingEdges (store : Store) (sourceId : ObjectId)
    (field : FieldAccess) : List ObjectEdge :=
  sortEdgesByIndex (store.indexedMatchingEdgesUnsorted sourceId field)

def fieldAccess (fieldName : Name) (arguments : List Argument) : FieldAccess :=
  { name := fieldName, arguments := arguments }

def resolveValueFromNode (store : Store) (schema : Schema)
    (fieldName : Name) (arguments : List Argument)
    (sourceNode : ObjectNode) : Execution.Value ObjectRef :=
  match schema.lookupField sourceNode.typeName fieldName with
  | none => .null
  | some fieldDefinition =>
      let field := fieldAccess fieldName arguments
      if schema.getPossibleTypes fieldDefinition.outputType.namedType = [] then
        match sourceNode.lookupProperty? field with
        | none => .null
        | some property => property.toValue
      else if typeRefIsListLike fieldDefinition.outputType then
        .list ((store.indexedMatchingEdges sourceNode.id field).map
          (fun edge => .object edge.targetType
            (some (objectRefOfId edge.targetId))))
      else
        match store.firstMatchingEdge? sourceNode.id field none with
        | none => .null
        | some edge => .object edge.targetType
            (some (objectRefOfId edge.targetId))

def resolveValueAtNode (store : Store) (schema : Schema)
    (fieldName : Name) (arguments : List Argument)
    (sourceId : ObjectId) : Execution.Value ObjectRef :=
  match store.lookupNode? sourceId with
  | none => .null
  | some sourceNode =>
      store.resolveValueFromNode schema fieldName arguments sourceNode

def resolveValue (store : Store) (schema : Schema)
    (fieldName : Name) (arguments : List Argument)
    (runtimeType : Name) : Execution.Value ObjectRef :=
  match store.firstNodeWithType? runtimeType with
  | none => .null
  | some sourceNode =>
      store.resolveValueFromNode schema fieldName arguments sourceNode

def nonListCompositeEdgeKeys (store : Store) : List FieldAccessKey :=
  store.edges.filterMap ObjectEdge.nonListKey?

def nonListCompositeEdgesUnique (store : Store) : Prop :=
  pairwiseUniqueByEqBool FieldAccessKey.eqBool store.nonListCompositeEdgeKeys

def listCompositeEdgeKeys (store : Store) : List ListIndexKey :=
  store.edges.filterMap ObjectEdge.listIndexKey?

def listCompositeEdgesUnique (store : Store) : Prop :=
  pairwiseUniqueByEqBool ListIndexKey.eqBool store.listCompositeEdgeKeys

def listCompositeEdgesDense (store : Store) : Prop :=
  ∀ edge, edge ∈ store.edges ->
    match edge.index? with
    | none => True
    | some index =>
        let edges := store.indexedMatchingEdges edge.sourceId edge.field
        index < edges.length
          ∧ ∀ expected, expected < edges.length ->
            ∃ candidate, candidate ∈ edges ∧ candidate.index? = some expected

def nodeIds (store : Store) : List ObjectId :=
  store.allNodes.map ObjectNode.id

def nodeIdsUnique (store : Store) : Prop :=
  pairwiseUniqueByEqBool (fun left right : ObjectId => left == right)
    store.nodeIds

def rootWellTyped (schema : Schema) (store : Store) : Prop :=
  schema.typeIncludesObject schema.queryType store.root.typeName

def edgeWellTyped (schema : Schema) (store : Store)
    (edge : ObjectEdge) : Prop :=
  ∃ sourceNode targetNode fieldDefinition,
    store.lookupNode? edge.sourceId = some sourceNode
      ∧ store.lookupNode? edge.targetId = some targetNode
      ∧ targetNode.typeName = edge.targetType
      ∧ schema.lookupField sourceNode.typeName edge.field.name = some fieldDefinition
      ∧ schema.getPossibleTypes fieldDefinition.outputType.namedType ≠ []
      ∧ edge.field.argumentsWellTyped schema fieldDefinition
      ∧ (typeRefIsListLike fieldDefinition.outputType = true ↔ edge.index?.isSome)
      ∧ schema.typeIncludesObject fieldDefinition.outputType.namedType targetNode.typeName

def wellTyped (schema : Schema) (store : Store) : Prop :=
  store.rootWellTyped schema
    ∧ store.nodeIdsUnique
    ∧ (∀ node, node ∈ store.allNodes -> node.wellTyped schema)
    ∧ (∀ edge, edge ∈ store.edges -> store.edgeWellTyped schema edge)
    ∧ store.nonListCompositeEdgesUnique
    ∧ store.listCompositeEdgesUnique
    ∧ store.listCompositeEdgesDense

end Store

namespace Store

def rootExecutionValue (store : Store) : Execution.Value ObjectRef :=
  .object store.root.typeName (some (objectRefOfId store.root.id))

def resolve (store : Store) (schema : Schema) (fieldName : Name)
    (arguments : List Argument) (source : Execution.Value ObjectRef) :
    Execution.Value ObjectRef :=
  match source with
  | .object runtimeType ref? =>
      match ref? with
      | some ref =>
          match objectIdOfRef? ref with
          | some sourceId =>
              match store.lookupNode? sourceId with
              | some sourceNode =>
                  if sourceNode.typeName == runtimeType then
                    store.resolveValueFromNode schema fieldName arguments sourceNode
                  else
                    .null
              | none =>
                  .null
          | none =>
              .null
      | none =>
          store.resolveValue schema fieldName arguments runtimeType
  | _ => .null

def resolvers (store : Store) (schema : Schema) : Execution.Resolvers ObjectRef :=
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
