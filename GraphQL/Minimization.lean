import GraphQL.Operation
import GraphQL.ResponseShape

namespace GraphQL

namespace Minimization

abbrev Shape := ResponseShape.Shape

structure Candidate (inputShape : Shape) where
  operation : Operation
  shape : Shape
  sameShape : ResponseShape.Shape.equivalent shape inputShape

def Candidate.size {inputShape : Shape} (candidate : Candidate inputShape) : Nat :=
  candidate.operation.size

def chooseSmaller {inputShape : Shape} (left right : Candidate inputShape) :
    Candidate inputShape :=
  if left.size ≤ right.size then left else right

def minimizeFrom {inputShape : Shape} (best : Candidate inputShape) :
    List (Candidate inputShape) -> Candidate inputShape
  | [] => best
  | candidate :: rest => minimizeFrom (chooseSmaller best candidate) rest

def minimize? {inputShape : Shape} : List (Candidate inputShape) -> Option (Candidate inputShape)
  | [] => none
  | candidate :: rest => some (minimizeFrom candidate rest)

theorem chooseSmaller_le_left {inputShape : Shape} (left right : Candidate inputShape) :
    (chooseSmaller left right).size ≤ left.size := by
  unfold chooseSmaller
  by_cases h : left.size ≤ right.size
  · simp [h]
  · simp [h]
    exact Nat.le_of_lt (Nat.lt_of_not_ge h)

theorem chooseSmaller_le_right {inputShape : Shape} (left right : Candidate inputShape) :
    (chooseSmaller left right).size ≤ right.size := by
  unfold chooseSmaller
  by_cases h : left.size ≤ right.size
  · simp [h]
  · simp [h]

theorem minimizeFrom_minimal {inputShape : Shape} (best : Candidate inputShape) :
    ∀ (rest : List (Candidate inputShape)) (candidate : Candidate inputShape),
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

theorem minimize?_minimal {inputShape : Shape} (candidates : List (Candidate inputShape))
    (output : Candidate inputShape) :
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
  shapeOf : Operation -> Shape
  candidates : (input : Operation) -> List (Candidate (shapeOf input))

def minimizeOperation? (spec : FragmentMinimizerSpec) (input : Operation) :
    Option (Candidate (spec.shapeOf input)) :=
  minimize? (spec.candidates input)

theorem minimizeOperation?_minimal (spec : FragmentMinimizerSpec) (input : Operation)
    (output : Candidate (spec.shapeOf input)) :
    minimizeOperation? spec input = some output ->
      ∀ candidate, candidate ∈ spec.candidates input -> output.size ≤ candidate.size := by
  intro h
  exact minimize?_minimal (spec.candidates input) output h

end Minimization

end GraphQL
