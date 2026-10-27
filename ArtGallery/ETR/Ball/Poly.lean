module

public import ArtGallery.ETR.Gate
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod

/-!
# Polynomial functions with explicit integer representations

`mon α x = ∏ j, x j ^ α j` is the monomial with exponent vector `α : Fin n → ℕ`, of degree
`deg α = ∑ j, α j`.  `PolyRep d L f` says that the real function `f` on `ℝ^n` is an integer linear
combination of monomials of degree `≤ d` whose coefficients have ℓ¹-norm `≤ L`; this class is
closed under sums and products with the obvious bounds.

For a system of gates we define the residuals `res g`, their directional derivatives `dres g`, and
the partial derivatives `dF S i` of the sum of squares `F = ∑_g (res g)²`, and show
`PolyRep 3 (18 * S.length) (dF S i)`.
-/

@[expose] public section

namespace ArtGallery.Ball

open Finset ArtGallery.Gate

variable {n : ℕ}

/-- The monomial with exponent vector `α`. -/
def mon (α : Fin n → ℕ) (x : Fin n → ℝ) : ℝ := ∏ j, x j ^ α j

/-- The total degree of an exponent vector. -/
def deg (α : Fin n → ℕ) : ℕ := ∑ j, α j

theorem mon_add (α β : Fin n → ℕ) (x : Fin n → ℝ) : mon (α + β) x = mon α x * mon β x := by
  simp only [mon, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem mon_zero (x : Fin n → ℝ) : mon 0 x = 1 := by
  simp [mon]

theorem mon_single (i : Fin n) (k : ℕ) (x : Fin n → ℝ) : mon (Pi.single i k) x = x i ^ k := by
  rw [mon, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem deg_add (α β : Fin n → ℕ) : deg (α + β) = deg α + deg β := by
  simp only [deg, Pi.add_apply, Finset.sum_add_distrib]

theorem deg_zero : deg (0 : Fin n → ℕ) = 0 := by
  simp [deg]

theorem deg_single (i : Fin n) (k : ℕ) : deg (Pi.single i k) = k := by
  rw [deg, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- `f` is an integer combination of monomials of degree `≤ d` with coefficient ℓ¹-norm `≤ L`. -/
def PolyRep (d L : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℤ) (β : ι → Fin n → ℕ),
    ∑ t, (c t).natAbs ≤ L ∧ (∀ t, deg (β t) ≤ d) ∧ ∀ x, f x = ∑ t, (c t : ℝ) * mon (β t) x

namespace PolyRep

theorem mono {d L d' L' : ℕ} {f : (Fin n → ℝ) → ℝ} (h : PolyRep d L f) (hd : d ≤ d')
    (hL : L ≤ L') : PolyRep d' L' f := by
  obtain ⟨ι, _, c, β, h1, h2, h3⟩ := h
  exact ⟨ι, inferInstance, c, β, h1.trans hL, fun t => (h2 t).trans hd, h3⟩

theorem congr {d L : ℕ} {f g : (Fin n → ℝ) → ℝ} (h : PolyRep d L f) (hfg : ∀ x, f x = g x) :
    PolyRep d L g := by
  obtain ⟨ι, _, c, β, h1, h2, h3⟩ := h
  exact ⟨ι, inferInstance, c, β, h1, h2, fun x => (hfg x).symm.trans (h3 x)⟩

theorem const (z : ℤ) : PolyRep (n := n) 0 z.natAbs (fun _ => (z : ℝ)) := by
  refine ⟨Unit, inferInstance, fun _ => z, fun _ => 0, ?_, fun _ => by rw [deg_zero], ?_⟩
  · simp
  · intro x
    simp [mon_zero]

theorem zero : PolyRep (n := n) 0 0 (fun _ => 0) := by
  simpa using const (n := n) 0

theorem indicator (p : Prop) [Decidable p] :
    PolyRep (n := n) 0 1 (fun _ => if p then (1 : ℝ) else 0) := by
  by_cases hp : p
  · simpa [hp] using const (n := n) 1
  · simpa [hp] using (zero (n := n)).mono le_rfl (Nat.zero_le 1)

theorem var (j : Fin n) : PolyRep 1 1 (fun x => x j) := by
  refine ⟨Unit, inferInstance, fun _ => 1, fun _ => Pi.single j 1, ?_,
    fun _ => by rw [deg_single], ?_⟩
  · simp
  · intro x
    simp [mon_single]

theorem add {d₁ d₂ L₁ L₂ : ℕ} {f g : (Fin n → ℝ) → ℝ} (hf : PolyRep d₁ L₁ f)
    (hg : PolyRep d₂ L₂ g) : PolyRep (max d₁ d₂) (L₁ + L₂) (fun x => f x + g x) := by
  obtain ⟨ι, _, c, β, h1, h2, h3⟩ := hf
  obtain ⟨κ, _, c', β', h1', h2', h3'⟩ := hg
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim c c', Sum.elim β β', ?_, ?_, ?_⟩
  · rw [Fintype.sum_sum_type]
    exact Nat.add_le_add h1 h1'
  · rintro (t | t)
    · exact (h2 t).trans (le_max_left _ _)
    · exact (h2' t).trans (le_max_right _ _)
  · intro x
    dsimp only
    rw [Fintype.sum_sum_type, h3, h3']
    rfl

theorem neg {d L : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : PolyRep d L f) :
    PolyRep d L (fun x => -f x) := by
  obtain ⟨ι, _, c, β, h1, h2, h3⟩ := hf
  refine ⟨ι, inferInstance, fun t => -c t, β, ?_, h2, ?_⟩
  · simpa using h1
  · intro x
    dsimp only
    rw [h3, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    push_cast
    ring

theorem sub {d₁ d₂ L₁ L₂ : ℕ} {f g : (Fin n → ℝ) → ℝ} (hf : PolyRep d₁ L₁ f)
    (hg : PolyRep d₂ L₂ g) : PolyRep (max d₁ d₂) (L₁ + L₂) (fun x => f x - g x) :=
  (hf.add hg.neg).congr fun _ => (sub_eq_add_neg _ _).symm

theorem mul {d₁ d₂ L₁ L₂ : ℕ} {f g : (Fin n → ℝ) → ℝ} (hf : PolyRep d₁ L₁ f)
    (hg : PolyRep d₂ L₂ g) : PolyRep (d₁ + d₂) (L₁ * L₂) (fun x => f x * g x) := by
  obtain ⟨ι, _, c, β, h1, h2, h3⟩ := hf
  obtain ⟨κ, _, c', β', h1', h2', h3'⟩ := hg
  refine ⟨ι × κ, inferInstance, fun p => c p.1 * c' p.2, fun p => β p.1 + β' p.2, ?_, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    simp only [Int.natAbs_mul]
    rw [← Finset.sum_mul_sum]
    exact Nat.mul_le_mul h1 h1'
  · rintro ⟨t, s⟩
    rw [deg_add]
    exact Nat.add_le_add (h2 t) (h2' s)
  · intro x
    dsimp only
    rw [h3, h3', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
    rw [mon_add]
    push_cast
    ring

theorem listSum {ι : Type*} {d L : ℕ} (l : List ι) (f : ι → (Fin n → ℝ) → ℝ)
    (hf : ∀ g ∈ l, PolyRep d L (f g)) :
    PolyRep d (L * l.length) (fun x => (l.map fun g => f g x).sum) := by
  induction l with
  | nil => simpa using (zero (n := n)).mono (Nat.zero_le d) le_rfl
  | cons g l ih =>
    have h1 := hf g (List.mem_cons_self ..)
    have h2 := ih fun g' hg' => hf g' (List.mem_cons_of_mem _ hg')
    refine ((h1.add h2).mono (by simp) (by rw [List.length_cons]; ring_nf; omega)).congr ?_
    intro x
    simp

end PolyRep

/-! ### Gates -/

/-- Extension of a point of `ℝ^n` by zero to an assignment of all variables. -/
def toSeq (x : Fin n → ℝ) : ℕ → ℝ := fun k => if h : k < n then x ⟨k, h⟩ else 0

/-- The residual of a gate: it vanishes exactly when the gate holds. -/
def res : Gate → (ℕ → ℝ) → ℝ
  | .one a, w => w a - 1
  | .add a b c, w => w a + w b - w c
  | .mul a b c, w => w a * w b - w c

/-- The derivative of the residual of a gate at `w` in direction `e`. -/
def dres : Gate → (ℕ → ℝ) → (ℕ → ℝ) → ℝ
  | .one a, e, _ => e a
  | .add a b c, e, _ => e a + e b - e c
  | .mul a b c, e, w => e a * w b + w a * e b - e c

/-- The `i`-th unit vector (as an assignment of all variables). -/
def unitVec (i : ℕ) : ℕ → ℝ := fun k => if k = i then 1 else 0

/-- The `i`-th partial derivative of `F = ∑_g (res g)²`. -/
def dF (S : List Gate) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  (S.map fun g => 2 * res g (toSeq x) * dres g (unitVec i) (toSeq x)).sum

theorem res_eq_zero_iff (g : Gate) (w : ℕ → ℝ) : res g w = 0 ↔ g.Holds w := by
  cases g <;> simp [res, Gate.Holds, sub_eq_zero]

theorem polyRep_toSeq (a : ℕ) : PolyRep (n := n) 1 1 (fun x => toSeq x a) := by
  by_cases ha : a < n
  · exact (PolyRep.var ⟨a, ha⟩).congr fun x => by simp [toSeq, ha]
  · exact (PolyRep.zero.mono (Nat.zero_le 1) (Nat.zero_le 1)).congr fun x => by simp [toSeq, ha]

theorem polyRep_unitVec (i a : ℕ) : PolyRep (n := n) 0 1 (fun _ => unitVec i a) :=
  PolyRep.indicator (a = i)

theorem polyRep_res (g : Gate) : PolyRep (n := n) 2 3 (fun x => res g (toSeq x)) := by
  cases g with
  | one a =>
    exact ((polyRep_toSeq a).sub (PolyRep.const 1)).mono (by simp) (by simp)
      |>.congr fun x => by simp [res]
  | add a b c =>
    exact (((polyRep_toSeq a).add (polyRep_toSeq b)).sub (polyRep_toSeq c)).mono (by simp)
      (by simp)
  | mul a b c =>
    exact (((polyRep_toSeq a).mul (polyRep_toSeq b)).sub (polyRep_toSeq c)).mono (by simp)
      (by simp)

theorem polyRep_dres (g : Gate) (i : ℕ) :
    PolyRep (n := n) 1 3 (fun x => dres g (unitVec i) (toSeq x)) := by
  cases g with
  | one a => exact (polyRep_unitVec i a).mono (Nat.zero_le 1) (by norm_num)
  | add a b c =>
    exact (((polyRep_unitVec i a).add (polyRep_unitVec i b)).sub (polyRep_unitVec i c)).mono
      (by simp) (by simp)
  | mul a b c =>
    exact ((((polyRep_unitVec i a).mul (polyRep_toSeq b)).add
      ((polyRep_toSeq a).mul (polyRep_unitVec i b))).sub (polyRep_unitVec i c)).mono
      (by simp) (by simp)

theorem polyRep_dF (S : List Gate) (i : Fin n) : PolyRep 3 (18 * S.length) (dF S i) := by
  have h : ∀ g ∈ S, PolyRep (n := n) 3 18
      (fun x => 2 * res g (toSeq x) * dres g (unitVec i) (toSeq x)) := fun g _ =>
    (((PolyRep.const 2).mul (polyRep_res g)).mul (polyRep_dres g i)).mono (by simp) (by simp)
      |>.congr fun x => by push_cast; ring
  exact PolyRep.listSum S _ h

end ArtGallery.Ball

end
