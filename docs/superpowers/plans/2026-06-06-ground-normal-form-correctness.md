# Ground Normal Form Correctness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove directive-free ground-type normal form correctness for `NormalForm.normalizeOperation` without adding assumptions to the public theorem statement.

**Architecture:** Keep the public theorem surface in `GraphQL/NormalForm.lean`, keep already-proven structural normality facts in `GraphQL/NormalForm/GroundTypeNormalization.lean`, and move the semantic proof ladder into focused follow-on modules under `GraphQL/NormalForm/GroundTypeNormalization/`. The proof follows GraphCoQL's Coq theorem `normalize_selections_preserves_semantics`: induction on normalization, with field-filter/partition lemmas and object-runtime grounding facts carrying the hard cases.

**Tech Stack:** Lean 4, Lake, GraphQL execution/model modules, GraphCoQL Coq reference in `/private/tmp/GraphCoQL-master`, and historical Lean branch `normal-form-3`.

---

## Reference Notes

- GraphCoQL source: `/private/tmp/GraphCoQL-master/src/theory/QuerySemanticsLemmas.v`.
- Main Coq theorem: `normalize_selections_preserves_semantics`, followed by `normalize_preserves_query_semantics`.
- Coq proof shape: `funelim (normalize_selections ...)`, then discharge each constructor with `filter_normalize_swap`, `filter_filter_absorb`, object possible-type membership, and recursive semantic preservation on child selections.
- Current branch difference: this Lean branch has no normalization fuel and executes through resolver functions, so the proof must use the current `normalizeSelectionSet` recursion and the current `Execution.collectFields`/`executeSelectionSet` semantics.
- `normal-form-3` supplies useful obligation names around `recursiveDirectiveFree...Correct`, but most of those statements are fuel-specific scaffolding. Do not port the fuel layer.

## File Structure

- Modify: `GraphQL/Execution.lean`
  - Add executable-field group algebra lemmas near `addExecutableField`, `addExecutableFields`, and `mergeExecutableGroups`.
- Create: `GraphQL/NormalForm/GroundTypeNormalization/FieldCollection.lean`
  - Prove directive-free collection correspondence for `validFieldsWithResponseName`, `withoutFieldsWithResponseName`, and `mergeSelectionSets`.
- Create: `GraphQL/NormalForm/GroundTypeNormalization/Semantics.lean`
  - Prove selection-set semantic preservation and lift it to `groundTypeNormalFormSemanticsPreservation`.
- Modify: `GraphQL/NormalForm/GroundTypeNormalization.lean`
  - Import the new modules only if the final theorem remains in this file; otherwise keep it as the structural module and let the new semantic module import it.
- Modify: `GraphQL.lean`
  - Import the final semantic module so `lake build` exposes the theorem.
- Modify: `docs/ground-type-normal-form-correctness-plan.md`
  - Update status after each completed proof slice.

## Task 1: Commit The Detailed Plan

**Files:**
- Create: `docs/superpowers/plans/2026-06-06-ground-normal-form-correctness.md`

- [ ] **Step 1: Verify the plan file is tracked**

Run:

```bash
git status --short docs/superpowers/plans/2026-06-06-ground-normal-form-correctness.md
```

Expected: the plan path appears as untracked.

- [ ] **Step 2: Commit the plan**

Run:

```bash
git add docs/superpowers/plans/2026-06-06-ground-normal-form-correctness.md
git commit -m "Plan ground normal form correctness proof"
```

Expected: commit succeeds and does not stage `AGENTS.md`.

## Task 2: Add Execution Group Algebra

**Files:**
- Modify: `GraphQL/Execution.lean`
- Test: temporary `/private/tmp/ground_norm_group_red.lean`

- [ ] **Step 1: Write red checks**

Create a temporary Lean file with:

```lean
import GraphQL.Execution

open GraphQL
open GraphQL.Execution

#check addExecutableFields_append
#check mergeExecutableGroups_nil_left
#check mergeExecutableGroups_nil_right
#check mergeExecutableGroups_assoc
```

Run:

```bash
lean /private/tmp/ground_norm_group_red.lean
```

Expected: FAIL because the lemmas do not exist.

- [ ] **Step 2: Add minimal group lemmas**

Add these theorem shapes near the grouped-field helpers:

```lean
theorem addExecutableFields_append
    (left right : List ExecutableField)
    (groups : List (Name × List ExecutableField)) :
    addExecutableFields (left ++ right) groups
      = addExecutableFields right (addExecutableFields left groups) := by
  induction left generalizing groups with
  | nil => simp [addExecutableFields]
  | cons field rest ih =>
      simp [addExecutableFields, ih]

theorem mergeExecutableGroups_nil_left
    (groups : List (Name × List ExecutableField)) :
    mergeExecutableGroups [] groups = groups := by
  induction groups with
  | nil => simp [mergeExecutableGroups]
  | cons group rest ih =>
      simp [mergeExecutableGroups, addExecutableGroup, addExecutableFields_append, ih]

theorem mergeExecutableGroups_nil_right
    (groups : List (Name × List ExecutableField)) :
    mergeExecutableGroups groups [] = groups := by
  simp [mergeExecutableGroups]

theorem mergeExecutableGroups_assoc
    (left middle right : List (Name × List ExecutableField)) :
    mergeExecutableGroups (mergeExecutableGroups left middle) right
      = mergeExecutableGroups left (mergeExecutableGroups middle right) := by
  induction right generalizing left middle with
  | nil => simp [mergeExecutableGroups]
  | cons group rest ih =>
      simp [mergeExecutableGroups, ih, addExecutableGroup, addExecutableFields_append]
```

- [ ] **Step 3: Verify group lemmas**

Run:

```bash
lean /private/tmp/ground_norm_group_red.lean
lake build GraphQL.Execution
```

Expected: both pass.

- [ ] **Step 4: Commit**

Run:

```bash
git add GraphQL/Execution.lean
git commit -m "Add execution group algebra lemmas"
```

Expected: commit succeeds and leaves unrelated files unstaged.

## Task 3: Add Field Collection Correspondence Skeleton

**Files:**
- Create: `GraphQL/NormalForm/GroundTypeNormalization/FieldCollection.lean`
- Modify: `GraphQL.lean`
- Test: temporary `/private/tmp/ground_norm_collection_red.lean`

- [ ] **Step 1: Write red checks**

Create a temporary Lean file with:

```lean
import GraphQL.NormalForm.GroundTypeNormalization.FieldCollection

open GraphQL
open GraphQL.NormalForm

#check collectFields_append
#check collectFields_inlineFragment_none_directiveFree
#check collectFields_inlineFragment_some_directiveFree_apply
```

Run:

```bash
lean /private/tmp/ground_norm_collection_red.lean
```

Expected: FAIL because the module and lemmas do not exist.

- [ ] **Step 2: Create the module**

The module header should be:

```lean
import GraphQL.NormalForm.GroundTypeNormalization

namespace GraphQL
namespace NormalForm
namespace GroundTypeNormalization
```

Add directive-free collection lemmas that expose the execution simplifications already proven in `GroundTypeNormalization.lean` under names usable by later semantic proofs:

```lean
theorem collectFields_append
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value)
    (left right : List Selection) :
    Execution.collectFields schema variableValues parentType source (left ++ right)
      =
    Execution.mergeExecutableGroups
      (Execution.collectFields schema variableValues parentType source left)
      (Execution.collectFields schema variableValues parentType source right) := by
  induction left with
  | nil =>
      simp [Execution.collectFields, Execution.mergeExecutableGroups_nil_left]
  | cons selection rest ih =>
      simp [Execution.collectFields, ih, Execution.mergeExecutableGroups_assoc]
```

Keep `collectFields_inlineFragment_none_directiveFree` and
`collectFields_inlineFragment_some_directiveFree_apply` as theorem aliases over the existing
`collectSelection_inlineFragment_*_noDirectives` lemmas so later proof code imports a semantic module instead of the structural module.

- [ ] **Step 3: Import the module**

Add to `GraphQL.lean`:

```lean
import GraphQL.NormalForm.GroundTypeNormalization.FieldCollection
```

- [ ] **Step 4: Verify**

Run:

```bash
lean /private/tmp/ground_norm_collection_red.lean
lake build
lake lint
```

Expected: all pass.

- [ ] **Step 5: Commit**

Run:

```bash
git add GraphQL.lean GraphQL/NormalForm/GroundTypeNormalization/FieldCollection.lean
git commit -m "Add field collection proof helpers"
```

Expected: commit succeeds.

## Task 4: Prove Selection-Set Preservation Core

**Files:**
- Modify: `GraphQL/NormalForm/GroundTypeNormalization/Semantics.lean`
- Modify: `GraphQL.lean`
- Test: temporary `/private/tmp/ground_norm_semantics_red.lean`

- [ ] **Step 1: Write red checks**

Create a temporary Lean file with:

```lean
import GraphQL.NormalForm.GroundTypeNormalization.Semantics

open GraphQL
open GraphQL.NormalForm
open GraphQL.NormalForm.GroundTypeNormalization

#check normalizeSelectionSet_executeSelectionSet
#check normalizeOperation_executeQuery
```

Run:

```bash
lean /private/tmp/ground_norm_semantics_red.lean
```

Expected: FAIL because the semantic module and theorems do not exist.

- [ ] **Step 2: Add the semantic module**

Use this header:

```lean
import GraphQL.NormalForm.GroundTypeNormalization.FieldCollection

namespace GraphQL
namespace NormalForm
namespace GroundTypeNormalization
```

Add `normalizeSelectionSet_executeSelectionSet` with these exact assumptions:

```lean
theorem normalizeSelectionSet_executeSelectionSet
    (schema : Schema)
    (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat)
    (parentType : Name)
    (source : Execution.Value)
    (selectionSet : List Selection)
    (hSchema : SchemaWellFormedness.schemaWellFormed schema)
    (hValid : Validation.selectionSetValid schema parentType selectionSet)
    (hDirectiveFree : selectionSetDirectiveFree selectionSet) :
    Execution.executeSelectionSet schema resolvers variableValues depth parentType source
      (normalizeSelectionSet schema parentType selectionSet)
      =
    Execution.executeSelectionSet schema resolvers variableValues depth parentType source
      selectionSet
```

Prove it by recursion on `normalizeSelectionSet.induct`. Each recursive call must use a validation projection lemma rather than strengthening the theorem.

- [ ] **Step 3: Add operation lift**

Add:

```lean
theorem normalizeOperation_executeQuery
    (schema : Schema)
    (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat)
    (operation : Operation)
    (source : Execution.Value)
    (hSchema : SchemaWellFormedness.schemaWellFormed schema)
    (hValid : Validation.operationDefinitionValid schema operation)
    (hDirectiveFree : operationDirectiveFree operation) :
    Execution.executeQuery schema resolvers variableValues depth
      (normalizeOperation schema operation) source
      =
    Execution.executeQuery schema resolvers variableValues depth operation source
```

Use `executeQuery_normalizeOperation_of_rootSource_not_apply` for the invalid-root branch and `groundTypeNormalFormSemanticsPreserved_of_executeSelectionSet` for the valid-root branch.

- [ ] **Step 4: Verify**

Run:

```bash
lean /private/tmp/ground_norm_semantics_red.lean
lake build
lake lint
```

Expected: all pass.

- [ ] **Step 5: Commit**

Run:

```bash
git add GraphQL.lean GraphQL/NormalForm/GroundTypeNormalization/Semantics.lean
git commit -m "Prove ground normalization semantic preservation"
```

Expected: commit succeeds.

## Task 5: Close Public Correctness Theorems

**Files:**
- Modify: `GraphQL/NormalForm/GroundTypeNormalization/Semantics.lean`
- Modify: `docs/ground-type-normal-form-correctness-plan.md`

- [ ] **Step 1: Prove the public proposition**

Add:

```lean
theorem groundTypeNormalFormSemanticsPreservation
    (schema : Schema) (operation : Operation) :
    NormalForm.groundTypeNormalFormSemanticsPreservation schema operation
```

Unfold `NormalForm.groundTypeNormalFormSemanticsPreservation` and use `normalizeOperation_executeQuery`.

- [ ] **Step 2: Prove store-backed correctness**

Add:

```lean
theorem groundNormalFormCorrect
    (schema : Schema) (operation : Operation) :
    NormalForm.groundNormalFormCorrect schema operation
```

Unfold `NormalForm.groundNormalFormCorrect` and use `groundNormalFormCorrect_of_semanticsPreservation`.

- [ ] **Step 3: Update status docs**

In `docs/ground-type-normal-form-correctness-plan.md`, mark the selection-set, operation, and store-backed steps complete. Mention that the proof follows GraphCoQL's `normalize_selections_preserves_semantics` strategy but uses the Lean execution collection model.

- [ ] **Step 4: Verify**

Run:

```bash
lake build
lake lint
```

Expected: both pass.

- [ ] **Step 5: Commit**

Run:

```bash
git add GraphQL/NormalForm/GroundTypeNormalization/Semantics.lean docs/ground-type-normal-form-correctness-plan.md
git commit -m "Close ground normal form correctness theorem"
```

Expected: commit succeeds.

## Self-Review

- Spec coverage: covers the requested plan, GraphCoQL consultation, `normal-form-3` consultation, proof support lemmas, semantic preservation, operation lift, and store-backed correctness.
- Placeholder scan: no `TBD`, `TODO`, or unspecified implementation steps.
- Type consistency: theorem names and module paths match the current branch names checked with `rg`.
