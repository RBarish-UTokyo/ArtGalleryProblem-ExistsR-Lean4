module

public import ArtGallery.ETR.Ball.NormalForm
public import ArtGallery.ETR.Ball.Bound
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Critical points are roots of characteristic polynomials

For a fixed variable `i`, multiplication by `x i` maps reduced monomials to combinations of reduced
monomials on the critical set (`rep_mon`); the matrix `M` of these combinations (entries in
`ℤ[δ]`) has the vector `(x^β)_β` as a left eigenvector with eigenvalue `x i`, so
`x i` is a root of `charpoly M` evaluated at `δ` (`exists_charpoly`).  The coefficients of
`charpoly M ∈ ℤ[δ][u]` are bounded by `ballH n S` (Leibniz formula).

`abs_le_of_tendsto` multiplies such a relation by `(1/δ)^D` (with `D` the largest `δ`-degree),
passes to the limit `δ → ∞`, and applies Cauchy's root bound (`cauchy_bound`) to the resulting
nonzero integer polynomial.
-/

@[expose] public section

namespace ArtGallery.Ball

open Polynomial Finset Filter Topology

variable {n : ℕ}

theorem deg_redExp_le (β : Red n) : deg (redExp β) ≤ 4 * n := by
  calc deg (redExp β) = ∑ j, (β j : ℕ) := rfl
    _ ≤ ∑ _j : Fin n, 4 := Finset.sum_le_sum fun j _ => Nat.lt_succ_iff.mp (β j).isLt
    _ = 4 * n := by simp [mul_comm]

theorem mon_redExp_zero (x : Fin n → ℝ) : mon (redExp (0 : Red n)) x = 1 := by
  simp [mon, redExp]

/-- **Characteristic polynomial relation.**  For every variable `i` there is a monic
`Q ∈ ℤ[δ][u]` with coefficients bounded by `ballH n S` such that `x i` is a root of `Q(δ, ·)`
whenever `x` satisfies the critical relations for `δ`. -/
theorem exists_charpoly {P : Fin n → (Fin n → ℝ) → ℝ} {S : ℕ} (hP : ∀ i, PolyRep 3 S (P i))
    (hS : 1 ≤ S) (i : Fin n) :
    ∃ Q : ℤ[X][X], Q.Monic ∧ polyNorm zNorm Q ≤ ballH n S ∧
      ∀ δ x, Crit P δ x → (Q.map (aeval δ).toRingHom).eval (x i) = 0 := by
  have h := fun α : Red n => rep_mon hP hS (redExp α + Pi.single i 1)
  choose c hc1 hc2 using h
  let M : Matrix (Red n) (Red n) ℤ[X] := fun β α => c α β
  refine ⟨M.charpoly, Matrix.charpoly_monic M, ?_, ?_⟩
  · have hE : ∀ β α, zNorm (M β α) ≤ S ^ (4 * n + 1) := by
      intro β α
      calc zNorm (M β α) ≤ ∑ β', zNorm (c α β') :=
            Finset.single_le_sum (f := fun β' => zNorm (c α β')) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ β)
        _ ≤ S ^ deg (redExp α + Pi.single i 1) := hc1 α
        _ ≤ S ^ (4 * n + 1) := Nat.pow_le_pow_right hS (by
            rw [deg_add, deg_single]
            have := deg_redExp_le α
            omega)
    have := polyNorm_charpoly_le subNorm_zNorm M _ hE
    have hcard : Fintype.card (Red n) = 5 ^ n := by simp
    rw [hcard] at this
    exact this
  · intro δ x hx
    rw [← Matrix.charpoly_map, Matrix.eval_charpoly, ← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨fun β => mon (redExp β) x, ?_, ?_⟩
    · intro h0
      have := congrFun h0 0
      simp only [mon_redExp_zero, Pi.zero_apply] at this
      exact one_ne_zero this
    · funext α
      have key := hc2 α δ x hx
      dsimp only at key
      rw [mon_add, mon_single, pow_one] at key
      simp only [Matrix.vecMul, dotProduct, Matrix.sub_apply, Matrix.scalar_apply,
        Matrix.diagonal_apply, Matrix.map_apply, Pi.zero_apply, mul_sub, Finset.sum_sub_distrib,
        mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [sub_eq_zero, ← key]
      refine Finset.sum_congr rfl fun β _ => ?_
      simp only [M, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      ring

/-- **Cauchy's bound.**  A real root of a nonzero integer polynomial with coefficients bounded
by `H` has absolute value at most `1 + H`. -/
theorem cauchy_bound (q : ℕ → ℤ) (K H : ℕ) (hq : ∃ k ≤ K, q k ≠ 0)
    (hH : ∀ k, (q k).natAbs ≤ H) (r : ℝ) (hr : ∑ k ∈ range (K + 1), (q k : ℝ) * r ^ k = 0) :
    |r| ≤ 1 + H := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨k₀, hk₀K, hk₀⟩ := hq
  set d := Nat.findGreatest (fun k => q k ≠ 0) K with hd
  have hqd : q d ≠ 0 := Nat.findGreatest_spec (P := fun k => q k ≠ 0) hk₀K hk₀
  have hdK : d ≤ K := Nat.findGreatest_le K
  have hzero : ∀ k, d < k → k ≤ K → q k = 0 := fun k h1 h2 => by
    have := Nat.findGreatest_is_greatest (P := fun k => q k ≠ 0) h1 h2
    push Not at this
    exact this
  have hsum : ∑ k ∈ range d, (q k : ℝ) * r ^ k + q d * r ^ d = 0 := by
    rw [← Finset.sum_range_succ, ← hr]
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) ?_
    intro k hk hk'
    simp only [Finset.mem_range] at hk hk'
    rw [hzero k (by omega) (by omega)]
    simp
  set s := |r| with hs
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hs1 : 1 < s := by linarith
  have hHs : (H : ℝ) < s - 1 := by linarith
  have hqH : ∀ k, |(q k : ℝ)| ≤ H := fun k => by
    rw [← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast hH k
  have hb : |∑ k ∈ range d, (q k : ℝ) * r ^ k| ≤ H * ∑ k ∈ range d, s ^ k := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_right (hqH k) (by positivity)
  have hG : (∑ k ∈ range d, s ^ k) * (s - 1) = s ^ d - 1 := geom_sum_mul s d
  have hGnn : 0 ≤ ∑ k ∈ range d, s ^ k := Finset.sum_nonneg fun k _ => by positivity
  have h1 : (H : ℝ) * ∑ k ∈ range d, s ^ k ≤ s ^ d - 1 := by
    rw [← hG, mul_comm]
    exact mul_le_mul_of_nonneg_left hHs.le hGnn
  have hqd1 : (1 : ℝ) ≤ |(q d : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hqd
  have hsd : 0 ≤ s ^ d := by positivity
  have h2 : s ^ d ≤ |(q d : ℝ) * r ^ d| := by
    rw [abs_mul, abs_pow, ← hs]
    nlinarith
  have h3 : (q d : ℝ) * r ^ d = -(∑ k ∈ range d, (q k : ℝ) * r ^ k) := by linarith
  rw [h3, abs_neg] at h2
  linarith

/-- The polynomial `∑_{k ≤ K} ∑_{j ≤ D} c j k a^(D-j) b^k` in two real variables. -/
def limPoly (K D : ℕ) (c : ℕ → ℕ → ℤ) (a b : ℝ) : ℝ :=
  ∑ k ∈ range (K + 1), ∑ j ∈ range (D + 1), (c j k : ℝ) * a ^ (D - j) * b ^ k

theorem tendsto_limPoly (K D : ℕ) (c : ℕ → ℕ → ℤ) {η u : ℕ → ℝ} {a₀ u₀ : ℝ}
    (hη : Tendsto η atTop (𝓝 a₀)) (hu : Tendsto u atTop (𝓝 u₀)) :
    Tendsto (fun t => limPoly K D c (η t) (u t)) atTop (𝓝 (limPoly K D c a₀ u₀)) := by
  unfold limPoly
  refine tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun j _ => ?_
  exact (tendsto_const_nhds.mul (hη.pow _)).mul (hu.pow _)

theorem limPoly_zero (K D : ℕ) (c : ℕ → ℕ → ℤ) (b : ℝ) :
    limPoly K D c 0 b = ∑ k ∈ range (K + 1), (c D k : ℝ) * b ^ k := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single D]
  · simp
  · intro j hj hjD
    have hj' : j < D + 1 := Finset.mem_range.mp hj
    have : D - j ≠ 0 := by omega
    simp [zero_pow this]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self D)) h

/-- **Passing to the limit.**  If `Q ≠ 0` has coefficient norm `≤ H`, `η t → 0⁺`, `u t → u₀`
and `u t` is a root of `Q(1/η t, ·)` for every `t`, then `|u₀| ≤ 1 + H`. -/
theorem abs_le_of_tendsto (Q : ℤ[X][X]) (hQ : Q ≠ 0) {H : ℕ} (hH : polyNorm zNorm Q ≤ H)
    (η u : ℕ → ℝ) (u₀ : ℝ) (hη0 : ∀ t, 0 < η t) (hη : Tendsto η atTop (𝓝 0))
    (hu : Tendsto u atTop (𝓝 u₀))
    (hrel : ∀ t, (Q.map (aeval (1 / η t)).toRingHom).eval (u t) = 0) : |u₀| ≤ 1 + H := by
  classical
  set K := Q.natDegree
  set D := Q.support.sup fun k => (Q.coeff k).natDegree with hDdef
  have hD : ∀ k, (Q.coeff k).natDegree ≤ D := by
    intro k
    by_cases hk : k ∈ Q.support
    · exact Finset.le_sup (f := fun k => (Q.coeff k).natDegree) hk
    · rw [notMem_support_iff.mp hk, natDegree_zero]
      exact Nat.zero_le _
  let c : ℕ → ℕ → ℤ := fun j k => (Q.coeff k).coeff j
  have hg0 : ∀ t, limPoly K D c (η t) (u t) = 0 := by
    intro t
    unfold limPoly
    have h := hrel t
    rw [eval_map, eval₂_eq_sum_range] at h
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
    have hη' : η t ≠ 0 := (hη0 t).ne'
    calc ∑ k ∈ range (K + 1), ∑ j ∈ range (D + 1), (c j k : ℝ) * η t ^ (D - j) * u t ^ k
        = η t ^ D * ∑ k ∈ range (K + 1), (aeval (1 / η t)) (Q.coeff k) * u t ^ k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [aeval_eq_sum_range' (n := D + 1) (Nat.lt_succ_of_le (hD k)), Finset.sum_mul,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjD : j ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          rw [zsmul_eq_mul]
          have hpow : η t ^ D = η t ^ (D - j) * η t ^ j := by
            rw [← pow_add, Nat.sub_add_cancel hjD]
          rw [hpow, one_div, inv_pow]
          field_simp
          simp only [c]
          ring
      _ = 0 := by rw [h, mul_zero]
  have hlim : Tendsto (fun t => limPoly K D c (η t) (u t)) atTop (𝓝 (limPoly K D c 0 u₀)) :=
    tendsto_limPoly K D c hη hu
  have hg00 : limPoly K D c 0 u₀ = 0 := by
    have hconst : Tendsto (fun t => limPoly K D c (η t) (u t)) atTop (𝓝 0) := by
      simp only [hg0]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim hconst
  rw [limPoly_zero] at hg00
  refine cauchy_bound (fun k => c D k) K H ?_ ?_ u₀ hg00
  · obtain ⟨k, hk, hkD⟩ := Finset.exists_mem_eq_sup Q.support (nonempty_support_iff.mpr hQ)
      (fun k => (Q.coeff k).natDegree)
    refine ⟨k, le_natDegree_of_mem_supp k hk, ?_⟩
    have hk0 : Q.coeff k ≠ 0 := mem_support_iff.mp hk
    show (Q.coeff k).coeff D ≠ 0
    rw [← hDdef] at hkD
    rw [hkD]
    exact leadingCoeff_ne_zero.mpr hk0
  · intro k
    calc (c D k).natAbs ≤ zNorm (Q.coeff k) := coeff_le_polyNorm subNorm_natAbs _ D
      _ ≤ polyNorm zNorm Q := coeff_le_polyNorm subNorm_zNorm Q k
      _ ≤ H := hH

end ArtGallery.Ball

end
