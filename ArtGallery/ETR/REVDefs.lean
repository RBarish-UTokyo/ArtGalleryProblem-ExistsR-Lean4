module

public import ArtGallery.Spec

/-!
# The problem ETR-INV-REV (Stade)

J. Stade, *The point-boundary art gallery problem is ∃ℝ-hard* (SoCG 2025), Definition 2.1:
an instance is a list of constraints

  `x = 1`,  `x · y ≥ 1`,  `x · (5/2 − y) ≤ 1`,  `x + y ≤ z`,  `x + y ≥ z`

on real variables `x i`, and the question is whether it has a solution with every variable in
`[1/2, 2]`.
-/

@[expose] public section

namespace ArtGallery.ETRINVREV

/-- A constraint of ETR-INV-REV on the variables `x i`. -/
inductive Constraint where
  /-- `x = 1`. -/
  | one (x : ℕ)
  /-- `x · y ≥ 1`. -/
  | invGe (x y : ℕ)
  /-- `x · (5/2 − y) ≤ 1`. -/
  | invRevLe (x y : ℕ)
  /-- `x + y ≤ z`. -/
  | addLe (x y z : ℕ)
  /-- `x + y ≥ z`. -/
  | addGe (x y z : ℕ)

/-- The constraint holds under the assignment `v`. -/
def Constraint.Holds (v : ℕ → ℝ) : Constraint → Prop
  | .one x => v x = 1
  | .invGe x y => 1 ≤ v x * v y
  | .invRevLe x y => v x * (5 / 2 - v y) ≤ 1
  | .addLe x y z => v x + v y ≤ v z
  | .addGe x y z => v z ≤ v x + v y

/-- Every variable of the constraint has index less than `n`. -/
def Constraint.VarsLt (n : ℕ) : Constraint → Prop
  | .one x => x < n
  | .invGe x y => x < n ∧ y < n
  | .invRevLe x y => x < n ∧ y < n
  | .addLe x y z => x < n ∧ y < n ∧ z < n
  | .addGe x y z => x < n ∧ y < n ∧ z < n

/-- An instance has a solution with every variable in `[1/2, 2]`. -/
def Satisfiable (Φ : List Constraint) : Prop :=
  ∃ v : ℕ → ℝ, (∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) ∧ ∀ c ∈ Φ, c.Holds v

end ArtGallery.ETRINVREV

end
