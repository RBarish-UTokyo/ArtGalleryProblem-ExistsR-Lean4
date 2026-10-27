module

public import ArtGallery.Spec

/-!
# Systems of ETR^{1,+,·} equations

An instance of the problem ETR^{1,+,·} (Definition 15 of the paper, with `c = 1`) is a list of
equations `x = 1`, `x + y = z`, `x · y = z` on real variables `x 0, x 1, …`.  These systems are
the intermediate stage of the reduction from ETR to ETR-INV:

* `ArtGallery.ETR.Circuit` translates a formula of ETR into such a system (the analogue of the
  paper's Lemma 17 and of the paragraph "Reduction to ETR^{1,+,·}");
* `ArtGallery.ETR.Ball` proves that a solvable system has a solution of doubly exponential
  size (the paper's Corollary 18, due to Schaefer and Štefankovič, proved here from scratch);
* `ArtGallery.ETR.Chain` performs the reductions to ETR^{1/8,+,·}_{[-1/8,1/8]},
  ETR^{1,+,·}_{[1/2,2]} and ETR-INV.
-/

@[expose] public section

namespace ArtGallery.Gate

/-- An equation of ETR^{1,+,·}. -/
inductive Gate where
  /-- `x = 1`. -/
  | one (x : ℕ)
  /-- `x + y = z`. -/
  | add (x y z : ℕ)
  /-- `x · y = z`. -/
  | mul (x y z : ℕ)
  deriving DecidableEq

/-- The equation holds under the assignment `v`. -/
def Gate.Holds (v : ℕ → ℝ) : Gate → Prop
  | .one x => v x = 1
  | .add x y z => v x + v y = v z
  | .mul x y z => v x * v y = v z

/-- Every variable of the equation has index less than `n`. -/
def Gate.VarsLt (n : ℕ) : Gate → Prop
  | .one x => x < n
  | .add x y z => x < n ∧ y < n ∧ z < n
  | .mul x y z => x < n ∧ y < n ∧ z < n

/-- `v` solves the system `S`. -/
def Solves (S : List Gate) (v : ℕ → ℝ) : Prop := ∀ g ∈ S, g.Holds v

/-- The exponent of the radius bound: a solvable system with `n` variables and `m` equations has
a solution in the box `[-2^(2^(ballExp n m)), 2^(2^(ballExp n m))]^n`. -/
def ballExp (n m : ℕ) : ℕ := 8 * (n + m + 2)

end ArtGallery.Gate

end
