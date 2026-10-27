module

public import ArtGallery.ETR.Gate
public import ArtGallery.ETR.Ball.Analysis
public import ArtGallery.ETR.Ball.Charpoly

/-!
# Solvable ETR^{1,+,·} systems have doubly exponentially bounded solutions

This is the analogue of Corollary 18 of the paper (Schaefer and Štefankovič): a solvable system of
`m` equations of the forms `x = 1`, `x + y = z`, `x · y = z` in `n` variables has a solution with
every coordinate of absolute value at most `2 ^ 2 ^ ballExp n m`.

The proof (in `ArtGallery/ETR/Ball/`) is elementary.  Perturb the sum of squares `F` of the
residuals by `ε · ∑ x_i⁶` and take global minimisers (`Ball.Analysis`); they satisfy the critical
relations `x_i⁵ = -δ ∂_i F` with `δ = 1/(6ε)` and converge, along a subsequence, to a solution.
Modulo the critical relations every monomial reduces to the `5^n` monomials with exponents
`< 5` (`Ball.NormalForm`), so each coordinate of a critical point is a root of the characteristic
polynomial of a multiplication matrix with entries in `ℤ[δ]` and explicitly bounded coefficients
(`Ball.Norm`, `Ball.Charpoly`).  Multiplying by a power of `1/δ` and letting `δ → ∞` gives a
nonzero integer polynomial vanishing at the coordinate of the limit, and Cauchy's root bound
finishes the proof (`Ball.Bound` does the arithmetic).
-/

@[expose] public section

namespace ArtGallery.Gate

open ArtGallery.Ball Filter Topology

/-- **Ball theorem.** A solvable system has a solution in the box of radius
`2 ^ 2 ^ ballExp n m`. -/
theorem ball_bound (S : List Gate) (n : ℕ) (hS : ∀ g ∈ S, g.VarsLt n)
    (h : ∃ v, Solves S v) :
    ∃ v, Solves S v ∧ ∀ i, |v i| ≤ (2 : ℝ) ^ 2 ^ ballExp n S.length := by
  obtain ⟨v, hv⟩ := h
  have ha := sqSum_eq_zero_of_solves hS hv
  obtain ⟨ystar, hstar, y, η, hη0, hη, hy, hcrit⟩ := exists_limit S _ ha
  refine ⟨toSeq ystar, solves_of_sqSum_eq_zero hstar, fun k => ?_⟩
  have hP : ∀ i : Fin n, PolyRep 3 (18 * S.length + 1) (dF S i) := fun i =>
    (polyRep_dF S i).mono le_rfl (Nat.le_succ _)
  have hcoord : ∀ i : Fin n, |ystar i| ≤ 1 + ballH n (18 * S.length + 1) := by
    intro i
    obtain ⟨Q, hQm, hQn, hQrel⟩ := exists_charpoly hP (Nat.le_add_left 1 _) i
    exact abs_le_of_tendsto Q hQm.ne_zero hQn η (fun t => y t i) (ystar i) hη0 hη
      (tendsto_pi_nhds.mp hy i) (fun t => hQrel _ _ (hcrit t))
  have hbound : ((1 + ballH n (18 * S.length + 1) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ 2 ^ ballExp n S.length := by
    exact_mod_cast ballH_bound n S.length
  push_cast at hbound
  by_cases hk : k < n
  · simp only [toSeq, hk, ↓reduceDIte]
    exact (hcoord _).trans hbound
  · simp only [toSeq, hk, ↓reduceDIte, abs_zero]
    positivity

end ArtGallery.Gate

end
