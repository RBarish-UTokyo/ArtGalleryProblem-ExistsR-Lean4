module

public import ArtGallery.ETR.Ball.Norm
public import ArtGallery.ETR.Ball.Poly
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Normal forms of monomials modulo the critical relations

Fix functions `P i : ℝ^n → ℝ` (later the partial derivatives of the sum of squares) with
`PolyRep 3 S (P i)`.  A point `x` satisfies the *critical relations* for the parameter `δ` when
`x i ^ 5 = -(δ * P i x)` for all `i` (`Crit P δ x`).

The reduced exponent vectors are `Red n = Fin n → Fin 5`.  `Rep P L f` says that `f δ x` agrees,
on the critical set, with `∑_{β reduced} c_β(δ) x^β` for integer polynomials `c_β ∈ ℤ[δ]` of total
coefficient ℓ¹-norm `≤ L`.  The main result `rep_mon` says that every monomial `x^α` has such a
representation with `L = S ^ deg α`: reduce `x_i^5` by the critical relation, which lowers the
degree by at least `2`.
-/

@[expose] public section

namespace ArtGallery.Ball

open Polynomial Finset

variable {n : ℕ}

/-- The critical relations `x i ^ 5 = -(δ * P i x)`. -/
def Crit (P : Fin n → (Fin n → ℝ) → ℝ) (δ : ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ i, x i ^ 5 = -(δ * P i x)

/-- Reduced exponent vectors: all exponents are `< 5`. -/
abbrev Red (n : ℕ) := Fin n → Fin 5

/-- The exponent vector of a reduced exponent vector. -/
def redExp (β : Red n) : Fin n → ℕ := fun j => (β j : ℕ)

/-- `f` is represented on the critical set by a combination of reduced monomials with
coefficients in `ℤ[δ]` of total ℓ¹-norm `≤ L`. -/
def Rep (P : Fin n → (Fin n → ℝ) → ℝ) (L : ℕ) (f : ℝ → (Fin n → ℝ) → ℝ) : Prop :=
  ∃ c : Red n → ℤ[X], ∑ β, zNorm (c β) ≤ L ∧
    ∀ δ x, Crit P δ x → ∑ β, aeval δ (c β) * mon (redExp β) x = f δ x

theorem zNorm_C (z : ℤ) : zNorm (C z) = z.natAbs := polyNorm_C subNorm_natAbs z

theorem zNorm_X : zNorm (X : ℤ[X]) ≤ 1 := polyNorm_X subNorm_natAbs

namespace Rep

variable {P : Fin n → (Fin n → ℝ) → ℝ}

theorem mono {L L' : ℕ} {f : ℝ → (Fin n → ℝ) → ℝ} (h : Rep P L f) (hL : L ≤ L') :
    Rep P L' f := by
  obtain ⟨c, h1, h2⟩ := h
  exact ⟨c, h1.trans hL, h2⟩

theorem congr {L : ℕ} {f g : ℝ → (Fin n → ℝ) → ℝ} (h : Rep P L f)
    (hfg : ∀ δ x, Crit P δ x → f δ x = g δ x) : Rep P L g := by
  obtain ⟨c, h1, h2⟩ := h
  exact ⟨c, h1, fun δ x hx => (h2 δ x hx).trans (hfg δ x hx)⟩

theorem zero : Rep P 0 (fun _ _ => 0) :=
  ⟨0, by simp [subNorm_zNorm.map_zero], fun δ x _ => by simp⟩

theorem add {L₁ L₂ : ℕ} {f g : ℝ → (Fin n → ℝ) → ℝ} (hf : Rep P L₁ f) (hg : Rep P L₂ g) :
    Rep P (L₁ + L₂) (fun δ x => f δ x + g δ x) := by
  obtain ⟨c, h1, h2⟩ := hf
  obtain ⟨c', h1', h2'⟩ := hg
  refine ⟨c + c', ?_, fun δ x hx => ?_⟩
  · calc ∑ β, zNorm ((c + c') β) ≤ ∑ β, (zNorm (c β) + zNorm (c' β)) :=
          Finset.sum_le_sum fun β _ => subNorm_zNorm.add_le _ _
      _ ≤ L₁ + L₂ := by rw [Finset.sum_add_distrib]; exact Nat.add_le_add h1 h1'
  · dsimp only
    rw [← h2 δ x hx, ← h2' δ x hx, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [Pi.add_apply, map_add]
    ring

theorem zmul {L : ℕ} {f : ℝ → (Fin n → ℝ) → ℝ} (z : ℤ) (hf : Rep P L f) :
    Rep P (z.natAbs * L) (fun δ x => z * f δ x) := by
  obtain ⟨c, h1, h2⟩ := hf
  refine ⟨fun β => C z * c β, ?_, fun δ x hx => ?_⟩
  · calc ∑ β, zNorm (C z * c β) ≤ ∑ β, z.natAbs * zNorm (c β) :=
          Finset.sum_le_sum fun β _ => (subNorm_zNorm.mul_le _ _).trans (by rw [zNorm_C])
      _ ≤ z.natAbs * L := by rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ h1
  · dsimp only
    rw [← h2 δ x hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [map_mul, eq_intCast, map_intCast]
    ring

theorem negDelta {L : ℕ} {f : ℝ → (Fin n → ℝ) → ℝ} (hf : Rep P L f) :
    Rep P L (fun δ x => -(δ * f δ x)) := by
  obtain ⟨c, h1, h2⟩ := hf
  refine ⟨fun β => -(X * c β), ?_, fun δ x hx => ?_⟩
  · calc ∑ β, zNorm (-(X * c β)) ≤ ∑ β, zNorm (c β) := by
          refine Finset.sum_le_sum fun β _ => ?_
          rw [subNorm_zNorm.map_neg]
          refine (subNorm_zNorm.mul_le _ _).trans ?_
          calc zNorm X * zNorm (c β) ≤ 1 * zNorm (c β) := Nat.mul_le_mul_right _ zNorm_X
            _ = zNorm (c β) := one_mul _
      _ ≤ L := h1
  · dsimp only
    rw [← h2 δ x hx, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [map_neg, map_mul, aeval_X]
    ring

theorem finsetSum {ι : Type*} (s : Finset ι) (L : ι → ℕ) (f : ι → ℝ → (Fin n → ℝ) → ℝ)
    (hf : ∀ t ∈ s, Rep P (L t) (f t)) :
    Rep P (∑ t ∈ s, L t) (fun δ x => ∑ t ∈ s, f t δ x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (P := P))
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun t ht => hf t (Finset.mem_insert_of_mem ht)
    rw [Finset.sum_insert ha]
    exact (h1.add h2).congr fun δ x _ => by rw [Finset.sum_insert ha]

theorem red (β : Red n) : Rep P 1 (fun _ x => mon (redExp β) x) := by
  classical
  refine ⟨Pi.single β 1, ?_, fun δ x _ => ?_⟩
  · rw [Finset.sum_eq_single β]
    · simp only [Pi.single_eq_same]
      rw [← C_1, zNorm_C]
      rfl
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, subNorm_zNorm.map_zero]
    · intro h
      exact absurd (Finset.mem_univ β) h
  · rw [Finset.sum_eq_single β]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro h
      exact absurd (Finset.mem_univ β) h

end Rep

/-- **Normal forms.**  Every monomial `x^α` is represented on the critical set with coefficient
norm `≤ S ^ deg α`. -/
theorem rep_mon {P : Fin n → (Fin n → ℝ) → ℝ} {S : ℕ} (hP : ∀ i, PolyRep 3 S (P i))
    (hS : 1 ≤ S) (α : Fin n → ℕ) : Rep P (S ^ deg α) (fun _ x => mon α x) := by
  suffices h : ∀ d, ∀ α : Fin n → ℕ, deg α = d → Rep P (S ^ d) (fun _ x => mon α x) from
    h _ α rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro α hd
  subst hd
  by_cases hα : ∀ j, α j < 5
  · have hβ : redExp (fun j => (⟨α j, hα j⟩ : Fin 5)) = α := rfl
    have := Rep.red (P := P) (fun j => (⟨α j, hα j⟩ : Fin 5))
    rw [hβ] at this
    exact this.mono (Nat.one_le_pow _ _ hS)
  push Not at hα
  obtain ⟨i, hi⟩ := hα
  -- `α = α' + 5 e_i`
  set α' : Fin n → ℕ := α - Pi.single i 5 with hα'
  have hsplit : α = α' + Pi.single i 5 := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [hα', hi]
    · simp [hα', hj]
  have hdeg : deg α = deg α' + 5 := by
    rw [hsplit, deg_add, deg_single]
  obtain ⟨ι, _, c, β, h1, h2, h3⟩ := hP i
  have hrec : ∀ t, Rep P ((c t).natAbs * S ^ (deg α - 2))
      (fun δ x => (c t : ℝ) * mon (α' + β t) x) := by
    intro t
    have hlt : deg (α' + β t) < deg α := by
      rw [deg_add, hdeg]
      have := h2 t
      omega
    refine ((ih _ hlt (α' + β t) rfl).zmul (c t)).mono (Nat.mul_le_mul_left _ ?_)
    refine Nat.pow_le_pow_right hS ?_
    rw [deg_add, hdeg]
    have := h2 t
    omega
  have hsum := (Rep.finsetSum Finset.univ _ _ fun t _ => hrec t).negDelta
  refine (hsum.mono ?_).congr ?_
  · rw [← Finset.sum_mul]
    calc (∑ t, (c t).natAbs) * S ^ (deg α - 2) ≤ S * S ^ (deg α - 2) :=
          Nat.mul_le_mul_right _ h1
      _ = S ^ (deg α - 2 + 1) := by rw [pow_succ]; ring
      _ ≤ S ^ deg α := Nat.pow_le_pow_right hS (by omega)
  · intro δ x hx
    have hx' := hx i
    rw [h3 x] at hx'
    calc -(δ * ∑ t, (c t : ℝ) * mon (α' + β t) x)
        = mon α' x * -(δ * ∑ t, (c t : ℝ) * mon (β t) x) := by
          simp only [mon_add, Finset.mul_sum]
          rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          ring
      _ = mon α x := by
          rw [← hx', hsplit, mon_add, mon_single]

end ArtGallery.Ball

end
