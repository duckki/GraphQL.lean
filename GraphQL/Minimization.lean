import GraphQL.Operation

/-!
Spec reference: GraphQL September 2025.
- No direct GraphQL spec section defines operation minimization.
- 2.4 Operations, 2.9 Fragments, 5 Validation, and 6 Execution are the intended semantic
  background for any future equivalence predicate.
- Fidelity note: this file is project-specific proof scaffolding. It proves finite-list
  minimality for candidates already proven equivalent by an external predicate, but it
  does not define GraphQL operation equivalence or a spec-preserving candidate generator.
-/
namespace GraphQL

namespace Minimization

-- Spec-related candidate wrapper: non-spec structure bundling an operation with evidence
-- for an externally supplied equivalence predicate.
structure Candidate (equivalentToInput : Operation -> Prop) where
  operation : Operation
  equivalent : equivalentToInput operation

def Candidate.size {equivalentToInput : Operation -> Prop}
    (candidate : Candidate equivalentToInput) : Nat :=
  candidate.operation.size

def chooseSmaller {equivalentToInput : Operation -> Prop}
    (left right : Candidate equivalentToInput) :
    Candidate equivalentToInput :=
  if left.size ≤ right.size then left else right

def minimizeFrom {equivalentToInput : Operation -> Prop}
    (best : Candidate equivalentToInput) :
    List (Candidate equivalentToInput) -> Candidate equivalentToInput
  | [] => best
  | candidate :: rest => minimizeFrom (chooseSmaller best candidate) rest

def minimize? {equivalentToInput : Operation -> Prop} :
    List (Candidate equivalentToInput) -> Option (Candidate equivalentToInput)
  | [] => none
  | candidate :: rest => some (minimizeFrom candidate rest)

-- Spec-independent finite minimization theorem: proves smallest `Operation.size` among
-- supplied equivalent candidates, not semantic correctness of those candidates.
theorem chooseSmaller_le_left {equivalentToInput : Operation -> Prop}
    (left right : Candidate equivalentToInput) :
    (chooseSmaller left right).size ≤ left.size := by
  unfold chooseSmaller
  by_cases h : left.size ≤ right.size
  · simp [h]
  · simp [h]
    exact Nat.le_of_lt (Nat.lt_of_not_ge h)

theorem chooseSmaller_le_right {equivalentToInput : Operation -> Prop}
    (left right : Candidate equivalentToInput) :
    (chooseSmaller left right).size ≤ right.size := by
  unfold chooseSmaller
  by_cases h : left.size ≤ right.size
  · simp [h]
  · simp [h]

theorem minimizeFrom_minimal {equivalentToInput : Operation -> Prop}
    (best : Candidate equivalentToInput) :
    ∀ (rest : List (Candidate equivalentToInput))
      (candidate : Candidate equivalentToInput),
      candidate = best ∨ candidate ∈ rest ->
        (minimizeFrom best rest).size ≤ candidate.size := by
  intro rest
  induction rest generalizing best with
  | nil =>
      intro candidate h
      cases h with
      | inl heq =>
          rw [heq]
          simp [minimizeFrom]
      | inr hmem =>
          cases hmem
  | cons head tail ih =>
      intro candidate h
      simp [minimizeFrom]
      let next := chooseSmaller best head
      have hnext : (minimizeFrom next tail).size ≤ next.size :=
        ih next next (Or.inl rfl)
      cases h with
      | inl heq =>
          rw [heq]
          exact Nat.le_trans hnext (chooseSmaller_le_left best head)
      | inr hmem =>
          cases hmem with
          | head =>
              exact Nat.le_trans hnext (chooseSmaller_le_right best head)
          | tail _ htail =>
              exact ih next candidate (Or.inr htail)

theorem minimize?_minimal {equivalentToInput : Operation -> Prop}
    (candidates : List (Candidate equivalentToInput))
    (output : Candidate equivalentToInput) :
    minimize? candidates = some output ->
      ∀ candidate, candidate ∈ candidates -> output.size ≤ candidate.size := by
  intro h candidate hmem
  cases candidates with
  | nil =>
      cases hmem
  | cons first rest =>
      simp [minimize?] at h
      rw [← h]
      exact minimizeFrom_minimal first rest candidate (by
        cases hmem with
        | head => exact Or.inl rfl
        | tail _ htail => exact Or.inr htail)

structure FragmentMinimizerSpec where
  equivalent : Operation -> Operation -> Prop
  candidates : (input : Operation) -> List (Candidate (equivalent input))

-- Spec-related minimizer entry point: non-spec; delegates all GraphQL fidelity to
-- `FragmentMinimizerSpec.equivalent` and `candidates`.
def minimizeOperation? (spec : FragmentMinimizerSpec) (input : Operation) :
    Option (Candidate (spec.equivalent input)) :=
  minimize? (spec.candidates input)

theorem minimizeOperation?_minimal (spec : FragmentMinimizerSpec) (input : Operation)
    (output : Candidate (spec.equivalent input)) :
    minimizeOperation? spec input = some output ->
      ∀ candidate, candidate ∈ spec.candidates input -> output.size ≤ candidate.size := by
  intro h
  exact minimize?_minimal (spec.candidates input) output h

end Minimization

end GraphQL
