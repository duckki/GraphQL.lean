# Ground-Type Normal Form Correctness

This document summarizes the completed directive-free ground-type normal form
correctness proof. It is meant to explain what the theorem says and how the
proof is structured without walking through the low-level Lean proof scripts.

## What Is Normalized

`NormalForm.normalizeOperation` rewrites an operation selection set into the
project's ground-type normal form. It performs two semantic-preserving
transformations:

1. Fields with the same response name are merged into one field head whose child
   selection set contains the merged subselections from the original group.
2. Selections whose return type is abstract are grounded by replacing the child
   selection set with possible-object inline fragments. Each possible object
   type receives the recursively normalized child selections.

This is a project-specific normal form inspired by GraphCoQL, not a GraphQL
spec feature. The current proof is deliberately scoped to directive-free source
operations, so it does not need to reason about directive-sensitive
normalization.

## Final Statements

The public predicates live in `GraphQL/NormalForm.lean`.

- `NormalForm.groundTypeNormalFormSemanticsPreservation` says that, assuming a
  well-formed schema, a valid operation, and no directives in the operation, the
  original operation and its normalized operation execute equivalently for all
  resolver environments, variable values, explicit execution depths, and source
  values.
- `NormalForm.groundNormalFormCorrect` says the same transformation is correct
  for the store-backed data model, again under the same public assumptions.

The theorem witnesses are in
`GraphQL/NormalForm/GroundTypeNormalization/Semantics.lean`:

- `GraphQL.NormalForm.GroundTypeNormalization.groundTypeNormalFormSemanticsPreservation`
- `GraphQL.NormalForm.GroundTypeNormalization.groundNormalFormCorrect`

The assumptions are intentionally narrow:

- `SchemaWellFormedness.schemaWellFormed schema`
- `Validation.operationDefinitionValid schema operation`
- `operationDirectiveFree operation`

No resolver-insensitivity assumption, fuel assumption, named-fragment
assumption, or extra store invariant is added to the public theorem.

## Why Equivalence Quantifies Depth

Execution remains bounded, but normalization can change the syntax size of an
operation. If operation equivalence compared the default bounded entry point on
both sides, the original and normalized operations could use different
operation-derived depth bounds.

To avoid making a false size-preservation claim, the proof compares both
operations at the same explicit execution depth through
`Execution.executeQueryAtDepth`. The existing `Execution.executeQuery` entry
point still exists for executable use and supplies the default
operation-derived bound.

This makes the semantic statement stronger and cleaner: for any chosen depth,
normalization preserves execution at that same depth.

## Proof Shape

The proof follows the same big idea as the GraphCoQL normal-form correctness
argument: prove preservation for selection sets first, then lift that result to
operations and finally to store-backed execution.

At a high level, the Lean proof has four layers.

## 1. Validation Gives The Normalizer Enough Facts

The normalizer is syntactic, but the proof needs semantic facts about the source
operation. Those facts come from validation:

- field lookups are valid where normalized field heads are built,
- same-response-name fields are merge-compatible,
- merged fields have the same field name and arguments when they share a parent,
- recursive child selections are valid for the runtime object types that can
  appear under a field return type,
- inline fragments are only used where schema overlap and possible-type facts
  make sense.

This lets the proof keep the theorem assumptions at the operation level instead
of exposing implementation-specific preconditions.

## 2. The Main Induction Is Over `normalizeSelectionSet`

The central theorem is
`normalizeSelectionSet_executeSelectionSet`. It proves that executing a
directive-free, semantically ready, merge-valid selection set gives the same
response before and after `normalizeSelectionSet`.

The induction follows the normalizer's actual recursion. The important cases
are:

- Missing field lookup: normalization drops no executable behavior because the
  invalid field cannot contribute under the validated assumptions.
- Inline fragment without a type condition: normalization flattens it, and
  execution does the same for directive-free fragments.
- Inline fragment with a non-overlapping type condition: normalization skips it,
  and execution also skips it.
- Inline fragment with an overlapping type condition: when the runtime source
  applies, execution of the flattened fragment agrees with execution of the
  original fragment.
- Field head: normalization keeps one representative field and merges the child
  selection sets for all fields with the same response name.

## 3. Field Merging Preserves Field Execution

The field case is the proof's main semantic step.

Execution collects fields by response name and resolves one response entry for
each collected group. Normalization also groups fields by response name, but it
does so syntactically. The proof bridges those two views: the executable field
group collected by execution corresponds to the validated same-response-name
group used by the normalizer.

Validation's field-merge theorem then supplies the facts needed to show that
the normalized field head resolves the same field with the same arguments as the
original group. The only remaining difference is the child selection set, and
that is handled by the recursive selection-set preservation theorem.

## 4. Abstract Returns Select The Runtime Branch

For object return types, recursive preservation is direct: normalize the child
selection set under the object type and use the induction hypothesis.

For abstract return types, the normalized child selections are wrapped in one
inline fragment per possible object type. Execution of those fragments selects
exactly the branch matching the runtime object and skips the rest. Schema
well-formedness supplies the required possible-type object facts, and the proof
uses that to reduce the abstract case back to the same recursive preservation
argument.

## Operation And Store Lifts

Once selection-set preservation is proved, the operation-level theorem is a
small wrapper:

1. If the root source does not apply to the operation root type, both the
   original and normalized operation execute to an empty object response.
2. If the root source applies, validation gives root selection-set validity,
   merge validity, and semantic readiness. The selection-set preservation
   theorem applies directly.

The store-backed theorem then instantiates resolver-parametric equivalence with
`Store.resolvers`. The store model does not need a separate normalization
argument; it reuses the resolver-level semantic preservation theorem.

## What This Does Not Prove

This proof intentionally does not cover:

- directive-sensitive normalization,
- named fragments or fragment spreads,
- mutation or subscription execution,
- execution errors, `errors`, or `extensions`,
- response-shape minimization,
- broader operation transformation algorithms.

Those features remain outside the current scoped plain GraphQL fragment.
