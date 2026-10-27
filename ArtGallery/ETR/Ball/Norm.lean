module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Perm

/-!
# ℓ¹-type size functions on polynomial rings

For the ball theorem we need explicit bounds on the integer coefficients of the characteristic
polynomial of a matrix with entries in `ℤ[X]`.  We axiomatise a *submultiplicative size*
`ν : R → ℕ` (`SubNorm`), show that the ℓ¹-norm of the coefficients (`polyNorm ν`) is again such a
size on `R[X]`, and bound the size of a determinant via the Leibniz formula:
`ν (det A) ≤ (card ι)! * K ^ card ι` when all entries have size `≤ K`.

Applied to `Int.natAbs` this gives the ℓ¹-norm `zNorm` on `ℤ[X]` and `polyNorm zNorm` on
`ℤ[X][X]`.
-/

@[expose] public section

namespace ArtGallery.Ball

open Polynomial Finset

/-- A size function `ν : R → ℕ` that is subadditive, submultiplicative, symmetric, with
`ν 0 = 0` and `ν 1 ≤ 1`. -/
structure SubNorm {R : Type*} [CommRing R] (ν : R → ℕ) : Prop where
  map_zero : ν 0 = 0
  map_one_le : ν 1 ≤ 1
  map_neg : ∀ a, ν (-a) = ν a
  add_le : ∀ a b, ν (a + b) ≤ ν a + ν b
  mul_le : ∀ a b, ν (a * b) ≤ ν a * ν b

/-- The ℓ¹-norm (with respect to `ν`) of the coefficients of a polynomial. -/
def polyNorm {R : Type*} [CommRing R] (ν : R → ℕ) (p : R[X]) : ℕ :=
  p.sum fun _ a => ν a

section General

variable {R : Type*} [CommRing R] {ν : R → ℕ}

theorem SubNorm.sum_le (h : SubNorm ν) {ι : Type*} (s : Finset ι) (f : ι → R) :
    ν (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ν (f i) :=
  Finset.le_sum_of_subadditive ν h.map_zero.le h.add_le s f

theorem SubNorm.prod_le (h : SubNorm ν) {ι : Type*} (s : Finset ι) (f : ι → R) :
    ν (∏ i ∈ s, f i) ≤ ∏ i ∈ s, ν (f i) :=
  Finset.le_prod_of_submultiplicative ν h.map_one_le h.mul_le s f

theorem SubNorm.sub_le (h : SubNorm ν) (a b : R) : ν (a - b) ≤ ν a + ν b := by
  rw [sub_eq_add_neg]
  exact (h.add_le _ _).trans (by rw [h.map_neg])

/-- The norm can be computed over any finite superset of the support. -/
theorem polyNorm_eq_sum (h : SubNorm ν) (p : R[X]) {s : Finset ℕ} (hs : p.support ⊆ s) :
    polyNorm ν p = ∑ k ∈ s, ν (p.coeff k) :=
  Polynomial.sum_eq_of_subset _ (fun _ => h.map_zero) hs

theorem polyNorm_monomial (h : SubNorm ν) (k : ℕ) (a : R) :
    polyNorm ν (monomial k a) = ν a :=
  Polynomial.sum_monomial_index a _ h.map_zero

theorem polyNorm_C (h : SubNorm ν) (a : R) : polyNorm ν (C a) = ν a := by
  rw [← monomial_zero_left, polyNorm_monomial h]

theorem polyNorm_X (h : SubNorm ν) : polyNorm ν (X : R[X]) ≤ 1 := by
  rw [← monomial_one_one_eq_X, polyNorm_monomial h]
  exact h.map_one_le

theorem coeff_le_polyNorm (h : SubNorm ν) (p : R[X]) (k : ℕ) :
    ν (p.coeff k) ≤ polyNorm ν p := by
  by_cases hk : k ∈ p.support
  · rw [polyNorm, Polynomial.sum_def]
    exact Finset.single_le_sum (f := fun k => ν (p.coeff k)) (fun _ _ => Nat.zero_le _) hk
  · rw [Polynomial.notMem_support_iff.mp hk, h.map_zero]
    exact Nat.zero_le _

theorem polyNorm_zero : polyNorm ν (0 : R[X]) = 0 := by
  simp [polyNorm]

theorem polyNorm_neg (h : SubNorm ν) (p : R[X]) : polyNorm ν (-p) = polyNorm ν p := by
  rw [polyNorm_eq_sum h (-p) (s := p.support) (by rw [support_neg]), polyNorm_eq_sum h p le_rfl]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_neg, h.map_neg]

theorem polyNorm_add_le (h : SubNorm ν) (p q : R[X]) :
    polyNorm ν (p + q) ≤ polyNorm ν p + polyNorm ν q := by
  classical
  rw [polyNorm_eq_sum h (p + q) (s := p.support ∪ q.support) support_add,
    polyNorm_eq_sum h p (s := p.support ∪ q.support) Finset.subset_union_left,
    polyNorm_eq_sum h q (s := p.support ∪ q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [coeff_add]
  exact h.add_le _ _

theorem polyNorm_sum_le (h : SubNorm ν) {ι : Type*} (s : Finset ι) (f : ι → R[X]) :
    polyNorm ν (∑ i ∈ s, f i) ≤ ∑ i ∈ s, polyNorm ν (f i) :=
  Finset.le_sum_of_subadditive (polyNorm ν) polyNorm_zero.le (polyNorm_add_le h) s f

theorem polyNorm_mul_le (h : SubNorm ν) (p q : R[X]) :
    polyNorm ν (p * q) ≤ polyNorm ν p * polyNorm ν q := by
  rw [mul_eq_sum_sum]
  refine (polyNorm_sum_le h _ _).trans ?_
  have hq : ∀ i, polyNorm ν (q.sum fun j a => monomial (i + j) (p.coeff i * a)) ≤
      ν (p.coeff i) * polyNorm ν q := by
    intro i
    rw [Polynomial.sum_def]
    refine (polyNorm_sum_le h _ _).trans ?_
    rw [polyNorm, Polynomial.sum_def, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [polyNorm_monomial h]
    exact h.mul_le _ _
  refine (Finset.sum_le_sum fun i _ => hq i).trans ?_
  rw [← Finset.sum_mul]
  exact le_rfl

/-- The coefficient ℓ¹-norm is again a submultiplicative size. -/
theorem SubNorm.poly (h : SubNorm ν) : SubNorm (polyNorm ν) where
  map_zero := polyNorm_zero
  map_one_le := by
    rw [← C_1, polyNorm_C h]
    exact h.map_one_le
  map_neg := polyNorm_neg h
  add_le := polyNorm_add_le h
  mul_le := polyNorm_mul_le h

/-- Leibniz bound for determinants. -/
theorem SubNorm.det_le (h : SubNorm ν) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (K : ℕ) (hA : ∀ i j, ν (A i j) ≤ K) :
    ν A.det ≤ (Fintype.card ι).factorial * K ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  refine (h.sum_le _ _).trans ?_
  have hσ : ∀ σ : Equiv.Perm ι, ν (Equiv.Perm.sign σ • ∏ i, A (σ i) i) ≤ K ^ Fintype.card ι := by
    intro σ
    have hs : ν (Equiv.Perm.sign σ • ∏ i, A (σ i) i) = ν (∏ i, A (σ i) i) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · rw [hs, one_smul]
      · rw [hs, Units.neg_smul, one_smul, h.map_neg]
    rw [hs]
    refine (h.prod_le _ _).trans ?_
    calc ∏ i, ν (A (σ i) i) ≤ ∏ _i : ι, K := Finset.prod_le_prod fun i _ => hA _ _
      _ = K ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
  refine (Finset.sum_le_sum fun σ _ => hσ σ).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, smul_eq_mul]

/-- Entries of the characteristic matrix have size at most `1 + E`. -/
theorem polyNorm_charmatrix_le (h : SubNorm ν) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (E : ℕ) (hM : ∀ i j, ν (M i j) ≤ E) (i j : ι) :
    polyNorm ν (M.charmatrix i j) ≤ 1 + E := by
  by_cases hij : i = j
  · subst hij
    rw [Matrix.charmatrix_apply_eq]
    refine ((h.poly).sub_le _ _).trans ?_
    rw [polyNorm_C h]
    exact Nat.add_le_add (polyNorm_X h) (hM i i)
  · rw [Matrix.charmatrix_apply_ne _ _ _ hij, polyNorm_neg h, polyNorm_C h]
    exact (hM i j).trans (Nat.le_add_left _ _)

/-- Coefficient bound for the characteristic polynomial. -/
theorem polyNorm_charpoly_le (h : SubNorm ν) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (E : ℕ) (hM : ∀ i j, ν (M i j) ≤ E) :
    polyNorm ν M.charpoly ≤ (Fintype.card ι).factorial * (1 + E) ^ Fintype.card ι :=
  (h.poly).det_le _ _ (polyNorm_charmatrix_le h M E hM)

end General

/-- `Int.natAbs` is a submultiplicative size. -/
theorem subNorm_natAbs : SubNorm Int.natAbs where
  map_zero := rfl
  map_one_le := le_rfl
  map_neg := Int.natAbs_neg
  add_le := Int.natAbs_add_le
  mul_le a b := (Int.natAbs_mul a b).le

/-- The ℓ¹-norm of the coefficients of an integer polynomial. -/
def zNorm (p : ℤ[X]) : ℕ := polyNorm Int.natAbs p

theorem subNorm_zNorm : SubNorm zNorm := subNorm_natAbs.poly

end ArtGallery.Ball

end
