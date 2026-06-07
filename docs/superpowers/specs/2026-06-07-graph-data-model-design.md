# Graph-Based Data Model Design

## Goal

Switch the proof-facing data model from numeric object IDs to a graph-shaped
store whose object identity is the field-access path used to reach that object.

## Scope

This is a data-model migration, not a normalizer rewrite. The first
implementation slice should preserve the current resolver-facing execution API
and keep the ground normal-form proof endpoints compiling.

Out of scope for the first slice:

- changing operation syntax,
- changing validation,
- changing normal-form algorithms,
- adding directive-aware normalization,
- proving new GraphCoQL theorem families beyond the existing store-backed
  correctness surface.

## Core Model

The store should become graph-shaped, similar to GraphCoQL:

- object nodes represent typed runtime objects,
- scalar/null field values live as node properties,
- object relationships live as labeled edges,
- the root object is stored directly,
- all objects are identified by their access path from the root.

The key identity rule is:

> Same field-access path means the same object.

## Identity Types

Inside `GraphQL.DataModel`, define path-oriented types:

```lean
namespace GraphQL.DataModel

structure FieldAccess where
  name : Name
  arguments : List Argument := []

inductive PathStep where
  | field : FieldAccess -> PathStep
  | index : Nat -> PathStep

abbrev ObjectPath := List PathStep

end GraphQL.DataModel
```

Execution should not depend on the data model. Instead, make its internal
resolver/source values generic over an object identity type named
`ObjectIdentity`:

```lean
inductive Execution.Value (ObjectIdentity : Type) where
  | null
  | scalar (value : String)
  | object (typeName : Name) (identity : ObjectIdentity)
  | list (values : List (Value ObjectIdentity))
```

`GraphQL.DataModel` instantiates that generic identity with
`GraphQL.DataModel.ObjectPath`. There is no top-level `GraphQL.ObjectIdentity`
alias; data-model APIs should use `ObjectPath` directly.

## Store Shape

Replace the numeric-ID record store with graph-shaped data:

```lean
namespace GraphQL.DataModel

inductive PropertyValue where
  | null
  | scalar (value : String)
  | list (values : List PropertyValue)

structure ObjectNode where
  typeName : Name
  path : ObjectPath
  properties : List (FieldAccess × PropertyValue) := []

structure ObjectEdge where
  sourcePath : ObjectPath
  field : FieldAccess
  index? : Option Nat := none
  targetType : Name

structure Store where
  root : ObjectNode
  nodes : List ObjectNode := []
  edges : List ObjectEdge := []

end GraphQL.DataModel
```

The root object path is `[]`. `Store.nodes` contains non-root nodes; helpers
should expose the full node universe as `root :: nodes`.

## Path Derivation

Path derivation is deterministic and should not depend on target node storage
order.

For a source object at path `p` and field access `f`:

- singleton object field target path: `p ++ [.field f.canonical]`;
- list object field element target path: `p ++ [.field f.canonical, .index i]`.

Edges should store the logical graph relationship, while path derivation gives
the object identity passed to execution. Canonicalization keeps GraphQL argument
order and input-object field order out of object identity.

## Resolution

`Store.resolveValue` should become schema-aware:

```lean
def Store.resolveValue
    (store : Store) (schema : Schema)
    (fieldName : Name) (arguments : List Argument) :
    Value -> Value
```

Resolution behavior:

- non-object sources resolve to `.null`;
- unknown source paths resolve to `.null`;
- missing schema field definitions resolve to `.null`;
- leaf fields read `ObjectNode.properties`;
- singleton composite fields follow the edge with `index? = none` and return
  `.object targetType derivedPath`;
- list composite fields collect matching indexed edges in stored order and
  return `.list` of `.object targetType derivedPath` values.

`Store.resolvers` should close over both `schema` and `store`, so the public
execution bridge remains:

```lean
Execution.executeQuery schema (store.resolvers schema) variableValues operation root
```

## Conformance

`Store.wellTyped` should be strengthened to match the graph model:

- the root path is `[]`;
- every node has an object type;
- node paths are unique across `root :: nodes`;
- property field labels exist on the node type and conform to leaf/list-leaf
  output types;
- every edge source path resolves to a node;
- every edge field exists on the source node type;
- every edge target type is included in the field output named type;
- every edge target path resolves to a node of that target type;
- non-list composite fields have at most one edge per source path and field.

This keeps GraphCoQL’s useful uniqueness/cardinality discipline while preserving
this repo’s typed value conformance style.

## Compatibility Strategy

Preserve names where practical:

- keep `DataModel.Value.object typeName identity`,
- keep `Root.toExecutionValue`,
- keep `executeOperation` and `executeOperationAtDepth`,
- update `Store.resolvers` call sites to pass `schema`,
- update store bridge lemmas to reason about paths instead of numeric IDs.

The existing normal-form proof modules mostly treat object identity opaquely.
Changing `Execution.Value` from a concrete `Nat` identity to a generic
`ObjectIdentity` parameter should preserve that proof shape while avoiding an
`Execution -> DataModel` dependency.

## Tests

Add tests before implementation for:

- root path identity is `[]`;
- scalar property lookup still returns a scalar;
- singleton object field resolution returns path `source ++ [.field access]`;
- list object field resolution returns paths
  `source ++ [.field access, .index i]`;
- two resolutions of the same field-access path produce equal object identities;
- non-list object fields reject multiple matching edges under `Store.wellTyped`.

## Review Notes

This design deliberately keeps the graph model and its store-backed execution
bridge under root `DataModel`, specializing generic execution identities to
`ObjectPath`. Final response data remains identity-free.
