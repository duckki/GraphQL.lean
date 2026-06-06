# Ground-Type Normal Form Correctness Plan

This document records the proof plan for the directive-free ground-type normal
form correctness theorem.

## Public Statements

The public review surface lives in `GraphQL/NormalForm.lean`.

Current public predicates:

- `NormalForm.operationsEquivalent`: resolver-parametric operation equivalence.
- `NormalForm.groundTypeNormalFormSemanticsPreserved`: semantic preservation for
  `normalizeOperation`.
- `NormalForm.groundNormalFormCorrect`: store-backed correctness over
  `DataModel.operationsEquivalentOnData`.
- `NormalForm.groundTypeNormalFormSemanticsPreservation`: final theorem
  proposition for resolver-parametric semantic preservation.

The final theorem proposition has exactly these assumptions:

- `SchemaWellFormedness.schemaWellFormed schema`
- `Validation.operationDefinitionValid schema operation`
- `NormalForm.operationDirectiveFree operation`

Do not add any further assumption to this theorem statement without review.

## Proof Module Layout

All proof work belongs under `GraphQL/NormalForm/`.

Current module:

- `GraphQL/NormalForm/GroundTypeNormalization.lean`: central proof-facing module
  for directive-free ground-type normalization.

As the proof grows, split topic files under `GraphQL/NormalForm/` and import
them from `GroundTypeNormalization.lean`. Candidate files:

- `GroundTypeNormalization/DirectiveFree.lean`
- `GroundTypeNormalization/FieldCollection.lean`
- `GroundTypeNormalization/MergeSemantics.lean`
- `GroundTypeNormalization/AbstractGrounding.lean`
- `GroundTypeNormalization/SelectionSetCorrectness.lean`
- `GroundTypeNormalization/OperationCorrectness.lean`

Keep fuel out of the proof architecture. The current normalizer terminates by
structural descent on selection-set size, so proof statements should follow that
recursion rather than reintroducing synthetic bounds.

## Current Proven Slice

The current proof-facing module already proves directive-freeness preservation
for the structural normalization helpers and for `normalizeOperation`.

This supports the later semantic proof by ensuring the directive-free source
assumption is stable across recursive normalized children.

The operation-level semantic bridge is also proven in
`GraphQL/NormalForm/GroundTypeNormalization/Semantics.lean`. The local
selection-set preservation induction now lifts to
`groundTypeNormalFormSemanticsPreservation` and then to
`groundNormalFormCorrect`. Because normalization intentionally changes syntax
size, the formal equivalence predicates quantify an explicit query execution
depth via `Execution.executeQueryAtDepth`; the bounded `Execution.executeQuery`
entry point remains available for executable use.

The GraphCoQL Coq reference theorem
`normalize_selections_preserves_semantics` proves the same high-level step by
induction over `normalize_selections`, using filter/partition swap lemmas and
possible-type object facts. The Lean proof now follows the same boundary, but
over this repo's resolver-backed `Execution.collectFields` and
`Execution.executeSelectionSet`.

## Proof Ladder

1. Directive-free structural preservation.

   Prove helper transformations preserve `selectionSetDirectiveFree` and
   `operationDirectiveFree`.

   Status: first slice is implemented in
   `GraphQL/NormalForm/GroundTypeNormalization.lean`.

2. Normal-form shape preservation.

   Prove `normalizeSelectionSet` produces `selectionSetNormal` under schema
   well-formedness and operation-derived selection validity.

   This step should use existing schema and operation validity facts. If the
   existing validity predicates do not expose a needed local induction
   invariant, add a derived lemma rather than strengthening the final theorem.

3. Field collection correspondence.

   Relate `validFieldsWithResponseName`, `withoutFieldsWithResponseName`, and
   `mergeSelectionSets` to execution's field collection behavior for
   directive-free selections.

   The target is a reusable statement that the normalizer partitions exactly the
   same executable field groups as execution sees for the current parent type.

   Status: execution-facing simplification lemmas are implemented in
   `GraphQL/NormalForm/GroundTypeNormalization/FieldCollection.lean`.
   During proof work, the generic ordered-map identity
   `mergeExecutableGroups [] groups = groups` was found to be false for
   arbitrary duplicate-key group lists. The current proof therefore tracks the
   collected-group invariant `executableGroupNamesNodup` and proves scoped
   merge associativity for collected groups. This is now strong enough to prove
   `collectFields_append` plus directive-free inline-fragment flattening for
   both untyped fragments and applicable typed fragments. Collected groups now
   also carry `executableGroupsWellFormed`, ensuring every executable field in a
   response-name group has the group key as its response name. The module also
   exposes `collectedResponseSelectionSet` and its merge behavior for nodup
   collected groups, which isolates the merged subselections for one response
   name. For concrete object parent execution, this projection is now proven to
   match `mergeSelectionSets (validFieldsWithResponseName ...)`.

4. Same-response-name merge semantics.

   Prove merging fields with the same response name preserves execution result
   for that response name.

   This step should rely on `Validation.operationDefinitionValid`, especially
   field merge validity, argument equivalence, and response-shape compatibility.

   Status: complete. `FieldMerge` exposes projection lemmas for pairwise merge
   validity, same-response-shape algebra, same-parent field/argument identity,
   and recursive subfield merge validity. The semantic proof connects those
   validation facts to collected executable response-name groups and proves the
   same-response-name field case through
   `normalizeSelectionSet_executeSelectionSet_field_head_case_of_recursive`.

5. Abstract return grounding.

   Prove replacing abstract child selections by one inline fragment per
   possible object type preserves execution.

   This step should rely on `SchemaWellFormedness.schemaWellFormed`, especially
   possible-type object validity and object/interface field implementation
   compatibility.

   Status: complete. The field semantic case now handles object returns by
   direct recursive preservation and abstract returns by wrapping normalized
   children in possible-type inline fragments, using
   `executeSelectionSet_possibleTypeFragments_runtime_branch` and schema
   possible-type object/nodup facts.

6. Selection-set semantic preservation.

   Prove by the actual `normalizeSelectionSet` recursion that executing a
   directive-free valid selection set is equivalent to executing its normalized
   form for every resolver environment, variable assignment, and source value.

   Status: complete. `normalizeSelectionSet_executeSelectionSet` is proved by
   the actual `normalizeSelectionSet.induct`, using the field merge/abstract
   grounding case, inline-fragment semantic case lemmas, semantic readiness
   projections, and merge-preservation lemmas for filtering and fragment
   flattening.

7. Operation semantic preservation.

   Lift selection-set preservation to `normalizeOperation`, using the metadata
   lemmas that normalization preserves operation name, root type, and variable
   definitions.

   This proves `NormalForm.groundTypeNormalFormSemanticsPreservation`.

   Status: complete. The lift from root-applicable selection-set preservation
   to resolver-parametric operation equivalence is implemented as
   `normalizeOperation_executeQuery`,
   `groundTypeNormalFormSemanticsPreservation_of_selectionSet`, and the final
   theorem witness `groundTypeNormalFormSemanticsPreservation`.

8. Store-backed correctness.

   Derive the store-backed correctness predicate
   `NormalForm.groundNormalFormCorrect` from resolver-parametric semantic
   preservation by instantiating resolvers with `Store.resolvers`.

   Status: complete. The lift from the same selection-set preservation theorem
   to store-backed correctness is implemented as
   `groundNormalFormCorrect_of_selectionSet` and the final theorem witness
   `groundNormalFormCorrect`.

## Non-Goals

- Do not prove directive-sensitive normalization in this theorem.
- Do not reintroduce named fragments or semantic operation inlining.
- Do not add fuel to normalizer definitions or correctness statements.
- Do not add theorem assumptions beyond schema well-formedness, operation
  validity, and directive-freeness without review.
