# Ground-Type Lifting

This note documents the phase 1 alternative normalization step:
ground-type lifting. It is separate from the existing ground normal form proof
notes because it is intended to become the new normalization pipeline, not a
minor variant of the current `normalizeSelectionSet` implementation.

Ground-type lifting is not a spec-conformance topic. It is an internal
operation transformation used to prepare a selection set for a later
simplification pass.

## Goal

The target pipeline is:

1. Ground-lift every field selection set.
2. Simplify each ground-type branch by applying the execution-relevant
   fragment applicability logic and merging selections with the same response
   name.

Only phase 1 is implemented now. Phase 2 is intentionally deferred.

The reason to split the algorithm is that phase 1 exposes every abstract field
return as explicit object-type branches. A later simplifier can then reason
locally inside each concrete runtime type branch, including directive handling.

## Phase 1 Algorithm

`groundLiftOperation` applies `groundLiftSelectionSet` to the operation root.
For each selection set, `groundLiftSelectionSet schema parentType selections`
transforms each selection under the current parent type.

For a field selection:

- If the field return type is a leaf type, the lifted field has an empty child
  selection set.
- If the field return type is an object type, the lifted field keeps its child
  selection set directly under the field. No extra inline fragment is added,
  because the field already has one possible runtime object type.
- If the field return type is an interface or union, the lifted field replaces
  its child selection set with one inline fragment per possible object type.
  Each branch contains a recursively lifted copy of the original child
  selection set under that object type.
- If field lookup fails, the implementation keeps recursing under the current
  parent type. This preserves the existing permissive raw-syntax behavior while
  validation remains responsible for ruling invalid operations out.

For an inline fragment selection:

- If the fragment has no type condition, keep the fragment and recursively lift
  its child selection set under the current parent type.
- If the fragment has a type condition, keep the fragment and recursively lift
  its child selection set under the fragment type condition.

## Example

For a field returning an abstract type:

```graphql
hero {
  id
  ... on Human {
    homePlanet
  }
}
```

If `hero` returns `Character` and the possible runtime object types are
`Human` and `Droid`, phase 1 produces:

```graphql
hero {
  ... on Human {
    id
    ... on Human {
      homePlanet
    }
  }
  ... on Droid {
    id
    ... on Human {
      homePlanet
    }
  }
}
```

This step intentionally does not remove inner inline fragments. That belongs to
phase 2, where the simplifier can apply fragment applicability rules inside
each already-grounded branch.

For a field returning an object type:

```graphql
human {
  id
  name
}
```

Phase 1 keeps the child selection set directly under the field:

```graphql
human {
  id
  name
}
```

It does not add a redundant `... on Human` wrapper.

## Semantic Preservation Boundary

The risk in this approach is phase 1: adding possible-object inline fragments
does not syntactically follow the execution algorithm step by step. The proof
obligation is therefore to show that the execution result is unchanged after
ground lifting.

The phase 1 operation wrapper lives in the separate module:

```lean
GraphQL.NormalForm.GroundTypeLifting.OperationSemantics
```

Directive handling is not a conceptual precondition for ground lifting. The
current theorem slice is directive-free because it reuses existing
directive-free execution and field-collection bridge lemmas. A directive-aware
completion should replace those helpers with lemmas that show the original
`@skip` and `@include` checks are evaluated exactly once on the single
runtime-matching lifted branch.

This module keeps only the resolver-parametric operation-level wrapper:

- `rootSourceAppliesBool_groundLiftOperation`
- `executeQueryWithFuel_groundLiftOperation_eq_of_selectionSet`

The remaining proof boundary is to re-establish selection-set preservation
directly over resolver-parametric execution, then continue with phase 2
simplification and directive-aware execution bridges. Object child returns
should still be covered without introducing a redundant object-type inline
fragment.

## Deferred Phase 2

Phase 2 should not call the existing `normalizeSelectionSet` directly. This
pipeline is meant to replace that implementation and eventually become
directive-aware.

The later simplifier should:

- Drop inline fragments whose type condition cannot apply to the current ground
  object type.
- Splice in children from inline fragments whose type condition does apply.
- Merge selections with the same response name according to the execution
  grouping behavior.
- Preserve or evaluate directives according to the directive-aware semantics
  added at that stage.

Until phase 2 exists, `groundLiftOperation` is a phase 1 transformation only.
The existing public normalizer remains unchanged.
