module

public import ArtGallery.ETR.Ball.NormalForm
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# The analytic part of the ball theorem

`sqSum S x = ∑_g (res g x)²` vanishes exactly on the solutions; `sixSum x = ∑_j x_j⁶`.
For `ε > 0` the perturbed objective `obj S ε = sqSum S + ε · sixSum` has a global minimiser `y`
with `sixSum y ≤ sixSum a` for any solution `a` (`exists_min`); at a global minimiser the
critical relations `y_i⁵ = -(1/(6ε)) · ∂_i sqSum (y)` hold (`crit_of_min`).  Letting `ε → 0`
along a convergent subsequence gives a solution `y*` which is the limit of critical points for
parameters `δ = 1/η_t → ∞` (`exists_limit`).
-/

@[expose] public section

namespace ArtGallery.Ball

open Finset Filter Topology ArtGallery.Gate

variable {n : ℕ}

/-- The sum of squares of the residuals. -/
def sqSum (S : List Gate) (x : Fin n → ℝ) : ℝ := (S.map fun g => res g (toSeq x) ^ 2).sum

/-- The coercive perturbation `∑_j x_j⁶`. -/
def sixSum (x : Fin n → ℝ) : ℝ := ∑ j, x j ^ 6

/-- The perturbed objective `sqSum + ε · sixSum`. -/
def obj (S : List Gate) (ε : ℝ) (x : Fin n → ℝ) : ℝ := sqSum S x + ε * sixSum x

theorem listSum_sq_nonneg (S : List Gate) (f : Gate → ℝ) : 0 ≤ (S.map fun g => f g ^ 2).sum := by
  induction S with
  | nil => simp
  | cons g S ih =>
    simp only [List.map_cons, List.sum_cons]
    positivity

theorem sqSum_nonneg (S : List Gate) (x : Fin n → ℝ) : 0 ≤ sqSum S x :=
  listSum_sq_nonneg S _

theorem sixSum_nonneg (x : Fin n → ℝ) : 0 ≤ sixSum x :=
  Finset.sum_nonneg fun j _ => by positivity

theorem eq_zero_of_listSum_sq (S : List Gate) (f : Gate → ℝ)
    (h : (S.map fun g => f g ^ 2).sum = 0) : ∀ g ∈ S, f g = 0 := by
  induction S with
  | nil => simp
  | cons g S ih =>
    simp only [List.map_cons, List.sum_cons] at h
    have h1 := sq_nonneg (f g)
    have h2 := listSum_sq_nonneg S f
    have hg : f g ^ 2 = 0 := by linarith
    have hS : (S.map fun g => f g ^ 2).sum = 0 := by linarith
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact pow_eq_zero_iff (two_ne_zero) |>.mp hg
    · exact ih hS g' hg'

theorem solves_of_sqSum_eq_zero {S : List Gate} {x : Fin n → ℝ} (h : sqSum S x = 0) :
    Solves S (toSeq x) := fun g hg =>
  (res_eq_zero_iff g _).mp (eq_zero_of_listSum_sq S (fun g => res g (toSeq x)) h g hg)

theorem sqSum_eq_zero_of_solves {S : List Gate} (hS : ∀ g ∈ S, g.VarsLt n) {v : ℕ → ℝ}
    (h : Solves S v) : sqSum S (fun j : Fin n => v j) = 0 := by
  have hres : ∀ g ∈ S, res g (toSeq fun j : Fin n => v j) = 0 := by
    intro g hg
    have hv := (res_eq_zero_iff g v).mpr (h g hg)
    have hvars := hS g hg
    have ht : ∀ k, k < n → toSeq (fun j : Fin n => v j) k = v k := fun k hk => by
      simp [toSeq, hk]
    cases g with
    | one a => simp only [res] at hv ⊢; rw [ht a hvars]; exact hv
    | add a b c =>
      obtain ⟨ha, hb, hc⟩ := hvars
      simp only [res] at hv ⊢; rw [ht a ha, ht b hb, ht c hc]; exact hv
    | mul a b c =>
      obtain ⟨ha, hb, hc⟩ := hvars
      simp only [res] at hv ⊢; rw [ht a ha, ht b hb, ht c hc]; exact hv
  unfold sqSum
  induction S with
  | nil => simp
  | cons g S ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [hres g (List.mem_cons_self ..), ih (fun g' hg' => hS g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hres g' (List.mem_cons_of_mem _ hg'))]
    simp

/-! ### Continuity -/

theorem continuous_toSeq (k : ℕ) : Continuous fun x : Fin n → ℝ => toSeq x k := by
  by_cases hk : k < n
  · simp only [toSeq, hk, ↓reduceDIte]
    exact continuous_apply _
  · simp only [toSeq, hk, ↓reduceDIte]
    exact continuous_const

theorem continuous_res (g : Gate) : Continuous fun x : Fin n → ℝ => res g (toSeq x) := by
  cases g with
  | one a => exact (continuous_toSeq a).sub continuous_const
  | add a b c => exact ((continuous_toSeq a).add (continuous_toSeq b)).sub (continuous_toSeq c)
  | mul a b c => exact ((continuous_toSeq a).mul (continuous_toSeq b)).sub (continuous_toSeq c)

theorem continuous_sqSum (S : List Gate) : Continuous (sqSum (n := n) S) := by
  unfold sqSum
  induction S with
  | nil => simpa using continuous_const
  | cons g S ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((continuous_res g).pow 2).add ih

theorem continuous_sixSum : Continuous (sixSum (n := n)) :=
  continuous_finsetSum _ fun j _ => (continuous_apply j).pow 6

theorem continuous_obj (S : List Gate) (ε : ℝ) : Continuous (obj (n := n) S ε) :=
  (continuous_sqSum S).add (continuous_const.mul continuous_sixSum)

/-! ### Derivatives along coordinate lines -/

/-- The line through `y` in direction `e_i`. -/
def line (y : Fin n → ℝ) (i : Fin n) (t : ℝ) : Fin n → ℝ :=
  fun j => y j + t * (if j = i then 1 else 0)

theorem line_zero (y : Fin n → ℝ) (i : Fin n) : line y i 0 = y := by
  funext j
  simp [line]

theorem toSeq_line (y : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    toSeq (line y i t) = fun k => toSeq y k + t * unitVec i k := by
  funext k
  by_cases hk : k < n
  · simp [toSeq, hk, unitVec, line, Fin.ext_iff]
  · have : k ≠ (i : ℕ) := by have := i.isLt; omega
    simp [toSeq, hk, unitVec, this]

theorem hasDerivAt_res (g : Gate) (w e : ℕ → ℝ) :
    HasDerivAt (fun t => res g (fun k => w k + t * e k)) (dres g e w) 0 := by
  have h1 : ∀ k, HasDerivAt (fun t : ℝ => w k + t * e k) (e k) 0 := fun k => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (e k)).const_add (w k)
  cases g with
  | one a => simpa [res, dres] using (h1 a).sub_const 1
  | add a b c => simpa [res, dres] using ((h1 a).fun_add (h1 b)).fun_sub (h1 c)
  | mul a b c => simpa [res, dres] using ((h1 a).fun_mul (h1 b)).fun_sub (h1 c)

theorem hasDerivAt_sqSum (S : List Gate) (y : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun t => sqSum S (line y i t)) (dF S i y) 0 := by
  have hsq : ∀ g : Gate, HasDerivAt
      (fun t => res g (fun k => toSeq y k + t * unitVec i k) ^ 2)
      (2 * res g (toSeq y) * dres g (unitVec i) (toSeq y)) 0 := by
    intro g
    have := (hasDerivAt_res g (toSeq y) (unitVec i)).fun_pow 2
    convert this using 1
    simp
  simp only [sqSum, toSeq_line]
  unfold dF
  induction S with
  | nil => simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  | cons g S ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hsq g).add ih

theorem hasDerivAt_sixSum (y : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun t => sixSum (line y i t)) (6 * y i ^ 5) 0 := by
  have h : ∀ j ∈ (Finset.univ : Finset (Fin n)), HasDerivAt
      (fun t : ℝ => (y j + t * (if j = i then 1 else 0)) ^ 6)
      ((6 : ℕ) * (y j + 0 * (if j = i then 1 else 0)) ^ (6 - 1) * (if j = i then 1 else 0)) 0 :=
    fun j _ => by
      simpa using
        (((hasDerivAt_id (0 : ℝ)).mul_const (if j = i then (1 : ℝ) else 0)).const_add
          (y j)).fun_pow 6
  have := HasDerivAt.fun_sum h
  have hfun : (fun t => sixSum (line y i t)) =
      fun t => ∑ j, (y j + t * (if j = i then 1 else 0)) ^ 6 := rfl
  rw [hfun]
  convert this using 1
  simp

theorem hasDerivAt_obj (S : List Gate) (ε : ℝ) (y : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun t => obj S ε (line y i t)) (dF S i y + ε * (6 * y i ^ 5)) 0 :=
  (hasDerivAt_sqSum S y i).add ((hasDerivAt_sixSum y i).const_mul ε)

/-- At a global minimiser of the perturbed objective the critical relations hold with
`δ = 1 / (6 ε)`. -/
theorem crit_of_min (S : List Gate) {ε : ℝ} (hε : 0 < ε) (y : Fin n → ℝ)
    (hy : ∀ z : Fin n → ℝ, obj S ε y ≤ obj S ε z) : Crit (dF S) (1 / (6 * ε)) y := by
  intro i
  have hmin : IsLocalMin (fun t => obj S ε (line y i t)) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    show obj S ε (line y i 0) ≤ obj S ε (line y i t)
    rw [line_zero]
    exact hy _
  have hderiv := hmin.hasDerivAt_eq_zero (hasDerivAt_obj S ε y i)
  have h6 : (6 * ε) ≠ 0 := by positivity
  have key : y i ^ 5 = -(dF S i y) / (6 * ε) := by
    rw [eq_div_iff h6]
    linear_combination hderiv
  rw [key]
  ring

/-! ### Minimisers and the limit -/

theorem isCompact_sublevel (C : ℝ) : IsCompact {y : Fin n → ℝ | sixSum y ≤ C} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le continuous_sixSum continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := max 1 C)).subset ?_
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right,
      pi_norm_le_iff_of_nonneg (le_trans zero_le_one (le_max_left _ _))]
    intro j
    have h6 : y j ^ 6 ≤ C :=
      (Finset.single_le_sum (f := fun k => y k ^ 6) (fun k _ => by positivity)
        (Finset.mem_univ j)).trans hy
    rw [Real.norm_eq_abs]
    by_cases h1 : |y j| ≤ 1
    · exact h1.trans (le_max_left _ _)
    · push Not at h1
      have h2 : |y j| ≤ |y j| ^ 6 := le_self_pow₀ h1.le (by norm_num)
      have h3 : |y j| ^ 6 = y j ^ 6 := by
        rw [← abs_pow, abs_of_nonneg (by positivity)]
      linarith [le_max_right 1 C]

theorem exists_min (S : List Gate) {ε : ℝ} (hε : 0 < ε) (a : Fin n → ℝ) (ha : sqSum S a = 0) :
    ∃ y : Fin n → ℝ, sixSum y ≤ sixSum a ∧ ∀ z : Fin n → ℝ, obj S ε y ≤ obj S ε z := by
  obtain ⟨y, hyK, hy⟩ := (isCompact_sublevel (sixSum a)).exists_isMinOn
    ⟨a, le_refl (sixSum a)⟩ (continuous_obj S ε).continuousOn
  refine ⟨y, hyK, fun z => ?_⟩
  by_cases hz : sixSum z ≤ sixSum a
  · exact isMinOn_iff.mp hy z hz
  · push Not at hz
    calc obj S ε y ≤ obj S ε a := isMinOn_iff.mp hy a (le_refl (sixSum a))
      _ = ε * sixSum a := by simp [obj, ha]
      _ ≤ ε * sixSum z := by gcongr
      _ ≤ obj S ε z := by
          have := sqSum_nonneg S z
          simp only [obj]
          linarith

/-- **The limit point.**  If `S` has a solution `a`, there are critical points `y t` for the
parameters `1 / η t` (with `η t → 0⁺`) converging to a solution `y*`. -/
theorem exists_limit (S : List Gate) (a : Fin n → ℝ) (ha : sqSum S a = 0) :
    ∃ ystar : Fin n → ℝ, sqSum S ystar = 0 ∧ ∃ (y : ℕ → Fin n → ℝ) (η : ℕ → ℝ),
      (∀ t, 0 < η t) ∧ Tendsto η atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 ystar) ∧
      ∀ t, Crit (dF S) (1 / η t) (y t) := by
  have hε : ∀ t : ℕ, (0 : ℝ) < 1 / (6 * ((t : ℝ) + 1)) := fun t => by positivity
  choose y hyK hymin using fun t : ℕ => exists_min S (hε t) a ha
  obtain ⟨ystar, -, φ, hφ, hlim⟩ := (isCompact_sublevel (sixSum a)).tendsto_subseq hyK
  have hη : Tendsto (fun t => 1 / ((φ t : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
  refine ⟨ystar, ?_, y ∘ φ, fun t => 1 / ((φ t : ℝ) + 1), fun t => by positivity, hη, hlim, ?_⟩
  · have hup : ∀ t, sqSum S ((y ∘ φ) t) ≤ sixSum a / 6 * (1 / ((φ t : ℝ) + 1)) := by
      intro t
      have h1 := hymin (φ t) a
      simp only [obj, ha, zero_add] at h1
      have h2 : 0 ≤ 1 / (6 * ((φ t : ℝ) + 1)) * sixSum (y (φ t)) :=
        mul_nonneg (hε _).le (sixSum_nonneg _)
      have h3 : sixSum a / 6 * (1 / ((φ t : ℝ) + 1)) = 1 / (6 * ((φ t : ℝ) + 1)) * sixSum a := by
        field_simp
      rw [h3]
      simp only [Function.comp]
      linarith
    have hlimF : Tendsto (fun t => sqSum S ((y ∘ φ) t)) atTop (𝓝 (sqSum S ystar)) :=
      ((continuous_sqSum S).tendsto ystar).comp hlim
    have hlimB : Tendsto (fun t => sixSum a / 6 * (1 / ((φ t : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using hη.const_mul (sixSum a / 6)
    exact le_antisymm (le_of_tendsto_of_tendsto' hlimF hlimB hup) (sqSum_nonneg S ystar)
  · intro t
    have h := crit_of_min S (hε (φ t)) (y (φ t)) (hymin (φ t))
    have e1 : (1 : ℝ) / (6 * (1 / (6 * ((φ t : ℝ) + 1)))) = (φ t : ℝ) + 1 := by
      field_simp
    have e2 : (1 : ℝ) / (1 / ((φ t : ℝ) + 1)) = (φ t : ℝ) + 1 := by
      rw [one_div_one_div]
    rw [e1] at h
    rw [e2]
    exact h

end ArtGallery.Ball

end
