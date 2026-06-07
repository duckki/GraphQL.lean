# Graph Data Model Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the numeric-ID store model with a GraphCoQL-style graph store whose public object identity is a field-access path.

**Architecture:** Introduce `GraphQL.DataModel.ObjectPath` in the root `GraphQL.DataModel` module, make `Execution.Value` generic over an `ObjectIdentity` type parameter, and instantiate that parameter with `ObjectPath` in `GraphQL.DataModel`. Rework `DataModel.Store` into root/node/edge graph data while preserving the resolver-facing execution API and existing ground normal-form proof surface.

**Tech Stack:** Lean 4, Lake, existing `GraphQL.Execution`, `GraphQL.DataModel`, `GraphQL.DataModel.Store`, and `Tests` Lean libraries.

---

### Task 1: Root DataModel Identity Definitions And Failing Tests

**Files:**
- Modify: `GraphQL/Execution.lean`
- Modify: `GraphQL/DataModel.lean`
- Modify: `GraphQL.lean`
- Create: `Tests/DataModel.lean`
- Modify: `Tests.lean`

- [x] **Step 1: Write failing tests for path identities**

Create `Tests/DataModel.lean` with:

```lean
import GraphQL

namespace GraphQL
namespace Tests
namespace DataModel

open GraphQL.DataModel

def heroAccess : FieldAccess :=
  { name := "hero", arguments := [] }

def friendsAccess : FieldAccess :=
  { name := "friends", arguments := [] }

def heroPath : ObjectPath :=
  FieldAccess.childPath [] heroAccess

def firstFriendPath : ObjectPath :=
  FieldAccess.childListElementPath [] friendsAccess 0

theorem rootPathSmoke : ([] : ObjectPath) = ([] : ObjectPath) := by
  rfl

theorem singletonPathSmoke :
    heroPath = [.field heroAccess] := by
  rfl

theorem listElementPathSmoke :
    firstFriendPath = [.field friendsAccess, .index 0] := by
  rfl

end DataModel
end Tests
end GraphQL
```

Update `Tests.lean`:

```lean
import Tests.NormalForm
import Tests.DataModel
```

- [x] **Step 2: Run test to verify it fails**

Run: `lake build Tests.DataModel`

Expected: FAIL because `GraphQL.DataModel.FieldAccess` and `GraphQL.DataModel.ObjectPath` do not exist.

- [x] **Step 3: Add identity definitions**

Add to `GraphQL/DataModel.lean`:

```lean
import GraphQL.Operation

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

def childPath (sourcePath : ObjectPath) (field : FieldAccess) : ObjectPath :=
  sourcePath ++ [.field field]

def childListElementPath
    (sourcePath : ObjectPath) (field : FieldAccess) (index : Nat) :
    ObjectPath :=
  sourcePath ++ [.field field, .index index]

end FieldAccess

end DataModel

```

Update `GraphQL/Execution.lean` to make object identity generic:

```lean
inductive Value (ObjectIdentity : Type) where
| object (typeName : Name) (identity : ObjectIdentity)
```

- [x] **Step 4: Run identity tests**

Run: `lake build Tests.DataModel`

Expected: PASS.

### Task 2: Graph Store Shape And Resolution Tests

**Files:**
- Modify: `GraphQL/DataModel.lean`
- Modify: `GraphQL/DataModel/Store.lean`
- Modify: `GraphQL/NormalForm/GroundTypeNormalization/OperationSemantics.lean`
- Create/modify: `Tests/DataModel.lean`

- [x] **Step 1: Add failing resolver tests**

Extend `Tests/DataModel.lean` with a small schema and graph store:

```lean
def stringFieldDefinition (name : Name) : FieldDefinition :=
  { name := name, outputType := .named "String", arguments := [] }

def objectFieldDefinition (name typeName : Name) : FieldDefinition :=
  { name := name, outputType := .named typeName, arguments := [] }

def listObjectFieldDefinition (name typeName : Name) : FieldDefinition :=
  { name := name, outputType := .list (.named typeName), arguments := [] }

def graphSchema : Schema :=
  { queryType := "Query"
    types :=
      [ .object
          { name := "Query"
            fields :=
              [ objectFieldDefinition "hero" "Human"
              , listObjectFieldDefinition "friends" "Human"
              , stringFieldDefinition "version" ]
            interfaces := [] }
      , .object
          { name := "Human"
            fields := [ stringFieldDefinition "name" ]
            interfaces := [] } ] }

def versionAccess : FieldAccess :=
  { name := "version", arguments := [] }

def graphStore : Store :=
  { root :=
      { typeName := "Query"
        path := []
        properties := [(versionAccess, .scalar "1")] }
    nodes :=
      [ { typeName := "Human"
          path := FieldAccess.childPath [] heroAccess
          properties := [] }
      , { typeName := "Human"
          path := FieldAccess.childListElementPath [] friendsAccess 0
          properties := [] } ]
    edges :=
      [ { sourcePath := []
          field := heroAccess
          index? := none
          targetType := "Human" }
      , { sourcePath := []
          field := friendsAccess
          index? := some 0
          targetType := "Human" } ] }

theorem scalarPropertyResolutionSmoke :
    graphStore.resolveValue graphSchema "version" [] (.object "Query" [])
      = .scalar "1" := by
  rfl

theorem singletonEdgeResolutionSmoke :
    graphStore.resolveValue graphSchema "hero" [] (.object "Query" [])
      = .object "Human" (FieldAccess.childPath [] heroAccess) := by
  rfl

theorem listEdgeResolutionSmoke :
    graphStore.resolveValue graphSchema "friends" [] (.object "Query" [])
      = .list [.object "Human" (FieldAccess.childListElementPath [] friendsAccess 0)] := by
  rfl
```

- [x] **Step 2: Run tests to verify they fail**

Run: `lake build Tests.DataModel`

Expected: FAIL because `Store` still has the old numeric object-record shape.

- [x] **Step 3: Implement graph store**

Modify `GraphQL/DataModel.lean`:

- remove `ObjectId`;
- change `DataModel.Value.object` to carry `ObjectPath`;
- replace `FieldKey` with `FieldAccess` comparison helpers;
- add `PropertyValue`, `ObjectNode`, `ObjectEdge`, and graph-shaped `Store`;
- add `Store.allNodes`, `Store.lookupNode?`, and `Store.resolveValue`;
- add `Store.resolve`, `Store.resolvers`, `Root.toExecutionValue`, and
  `operationsEquivalentOnData` in `GraphQL.DataModel`.

- [x] **Step 4: Run resolver tests**

Run: `lake build Tests.DataModel`

Expected: PASS.

### Task 3: Store Well-Typed Bridge

**Files:**
- Modify: `GraphQL/DataModel.lean`
- Modify: `GraphQL/DataModel/Store.lean`

- [x] **Step 1: Add a duplicate non-list edge rejection test**

Extend `Tests/DataModel.lean`:

```lean
def duplicateHeroEdgeStore : Store :=
  { graphStore with
    edges :=
      graphStore.edges ++
        [{ sourcePath := []
           field := heroAccess
           index? := none
           targetType := "Human" }] }

theorem duplicateHeroEdgeRejected :
    ¬ duplicateHeroEdgeStore.nonListCompositeEdgesUnique := by
  simp [Store.nonListCompositeEdgesUnique, Store.nonListCompositeEdgeKeys,
    ObjectEdge.nonListKey?, duplicateHeroEdgeStore, graphStore]
```

- [x] **Step 2: Run test to verify failure**

Run: `lake build Tests.DataModel`

Expected: FAIL until uniqueness is part of the store model.

- [x] **Step 3: Update conformance definitions and bridge lemmas**

Implement:

```lean
namespace ObjectEdge

def nonListKey? (edge : ObjectEdge) : Option (ObjectPath × FieldAccess) :=
  match edge.index? with
  | none => some (edge.sourcePath, edge.field)
  | some _ => none

end ObjectEdge

namespace Store

def nonListCompositeEdgeKeys (store : Store) : List (ObjectPath × FieldAccess) :=
  store.edges.filterMap ObjectEdge.nonListKey?

def nonListCompositeEdgesUnique (store : Store) : Prop :=
  store.nonListCompositeEdgeKeys.Nodup

def wellTyped (schema : Schema) (store : Store) : Prop :=
  store.root.path = []
    ∧ (store.allNodes.map ObjectNode.path).Nodup
    ∧ (∀ node, node ∈ store.allNodes -> node.wellTyped schema)
    ∧ (∀ edge, edge ∈ store.edges -> edge.wellTyped schema store)
    ∧ store.nonListCompositeEdgesUnique

end Store
```

Update `GraphQL/DataModel/Store.lean` lemmas to path-based names:

- `lookupNode?_some_mem`,
- `lookupNode?_some_path`,
- `resolveValue_conformsToLookupField`,
- `object_conformsToType_typeIncludesObject`,
- `resolveValue_ne_scalar_of_compositeLookupField`.

- [x] **Step 4: Run store bridge build**

Run: `lake build GraphQL.DataModel.Store`

Expected: PASS.

### Task 4: Whole Project Verification

**Files:**
- All touched files.

- [x] **Step 1: Build project**

Run: `lake build`

Expected: PASS.

- [x] **Step 2: Lint project**

Run: `lake lint`

Expected: PASS.

- [x] **Step 3: Review diff**

Run: `git status --short` and `git diff --stat`.

Expected: only graph-data-model implementation, tests, spec, and plan files changed.
