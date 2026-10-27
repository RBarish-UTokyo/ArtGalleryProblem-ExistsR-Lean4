module

public import ArtGallery.Hardness.Sec5.CoverKind

/-!
# Section 5, sufficiency (vi): the canonical values satisfy the template constraints

For an assignment `x` satisfying `Φ`, the receiver values `recvVal n x left u` of every unit `u`
(right units: `left = false`, left units: `left = true`) satisfy the constraint `KindCons` of the
template of `u` (`right_cons`, `left_cons`):

* orientation units: the two values are `x_i` and `5/2 − x_i` (sum `5/2`);
* `≥`-addition (right): `x_c ≤ x_a + x_b`; `≤`-addition (left, values `5/2 − ·`):
  `(5/2 − x_c) + 5/2 ≤ (5/2 − x_b) + (5/2 − x_a)`;
* inversion: `x_a · x_b = 1`.
-/

@[expose] public section

namespace ArtGallery.Sec5.CoverT

open ArtGallery

variable {Φ : List ETRINV.Constraint} {n : ℕ} {x : ℕ → ℝ}

theorem slotVal_low {g i : ℕ} (hg : g < 3) (hi : i < n) : slotVal n x (g * n + i) = x i := by
  have h1 : g * n + i < 3 * n := by nlinarith
  have h2 : (g * n + i) % n = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  simp only [slotVal, h1, ite_true, h2]

theorem slotVal_high {i : ℕ} (hi : i < n) : slotVal n x (3 * n + i) = 5 / 2 - x i := by
  have h1 : ¬ 3 * n + i < 3 * n := by omega
  have h2 : (3 * n + i) % n = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  simp only [slotVal, h1, ite_false, h2]

theorem workVal_right (σ : ℕ) : workVal n x false σ = slotVal n x σ := by
  simp [workVal]

theorem workVal_left {σ : ℕ} (hσ : σ < 4 * n) :
    workVal n x true (workSlot n σ) = 5 / 2 - slotVal n x σ := by
  have : 4 * n - 1 - (4 * n - 1 - σ) = σ := by omega
  simp only [workVal, workSlot, ite_true, this]

/-- **The right units satisfy their template constraint.** -/
theorem right_cons (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hΦx : ∀ c ∈ Φ, c.Holds x) :
    ∀ u ∈ (unitSpecs n Φ).1, KindCons u.kind (recvVal n x false u) := by
  intro u hu
  simp only [unitSpecs, List.mem_append] at hu
  rcases hu with (hu | hu) | hu
  · simp only [orientR, List.mem_flatMap, List.mem_range, List.mem_map] at hu
    obtain ⟨i, hi, g, hg, rfl⟩ := hu
    simp only [KindCons, recvVal, List.length_cons, List.length_nil, workVal_right]
    simp only [show 0 + 1 + 1 - 1 - 1 = 0 by rfl, show 0 + 1 + 1 - 1 - 0 = 1 by rfl,
      List.getD_cons_zero, List.getD_cons_succ, slotVal_low hg hi, slotVal_high hi]
    linarith
  · simp only [List.mem_flatMap] at hu
    obtain ⟨c, hc, hu⟩ := hu
    have hv := hΦ c hc
    have hh := hΦx c hc
    cases c with
    | one _ => simp [addR] at hu
    | inv _ _ => simp [addR] at hu
    | add a b e =>
      simp only [addR, List.mem_cons, List.not_mem_nil, or_false] at hu
      subst hu
      simp only [ETRINV.Constraint.VarsLt] at hv
      simp only [ETRINV.Constraint.Holds] at hh
      obtain ⟨ha, hb, he⟩ := hv
      simp only [KindCons, recvVal, List.length_cons, List.length_nil, workVal_right]
      simp only [show 0 + 1 + 1 + 1 - 1 - 2 = 0 by rfl, show 0 + 1 + 1 + 1 - 1 - 1 = 1 by rfl,
        show 0 + 1 + 1 + 1 - 1 - 0 = 2 by rfl, List.getD_cons_zero, List.getD_cons_succ]
      rw [show a = 0 * n + a by ring, slotVal_low (by norm_num) ha,
        show n + b = 1 * n + b by ring, slotVal_low (by norm_num) hb,
        show 2 * n + e = 2 * n + e by ring, slotVal_low (by norm_num) he]
      linarith
  · simp only [List.mem_flatMap] at hu
    obtain ⟨c, hc, hu⟩ := hu
    have hv := hΦ c hc
    have hh := hΦx c hc
    cases c with
    | one _ => simp [invR] at hu
    | add _ _ _ => simp [invR] at hu
    | inv a b =>
      simp only [invR, List.mem_cons, List.not_mem_nil, or_false] at hu
      subst hu
      simp only [ETRINV.Constraint.VarsLt] at hv
      simp only [ETRINV.Constraint.Holds] at hh
      obtain ⟨ha, hb⟩ := hv
      simp only [KindCons, recvVal, List.length_cons, List.length_nil, workVal_right]
      simp only [show 0 + 1 + 1 - 1 - 1 = 0 by rfl, show 0 + 1 + 1 - 1 - 0 = 1 by rfl,
        List.getD_cons_zero, List.getD_cons_succ]
      rw [show a = 0 * n + a by ring, slotVal_low (by norm_num) ha, slotVal_high hb]
      rw [← hh]; ring

/-- **The left units satisfy their template constraint.** -/
theorem left_cons (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hΦx : ∀ c ∈ Φ, c.Holds x) :
    ∀ u ∈ (unitSpecs n Φ).2, KindCons u.kind (recvVal n x true u) := by
  intro u hu
  simp only [unitSpecs, List.mem_append] at hu
  rcases hu with hu | hu
  · simp only [orientL, List.mem_flatMap, List.mem_range, List.mem_map] at hu
    obtain ⟨i, hi, g, hg, rfl⟩ := hu
    simp only [KindCons, recvVal, List.length_cons, List.length_nil]
    simp only [show 0 + 1 + 1 - 1 - 1 = 0 by rfl, show 0 + 1 + 1 - 1 - 0 = 1 by rfl,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [workVal_left (by omega), workVal_left (by nlinarith), slotVal_low hg hi, slotVal_high hi]
    linarith
  · simp only [List.mem_flatMap] at hu
    obtain ⟨c, hc, hu⟩ := hu
    have hv := hΦ c hc
    have hh := hΦx c hc
    cases c with
    | one _ => simp [addL] at hu
    | inv _ _ => simp [addL] at hu
    | add a b e =>
      simp only [addL, List.mem_cons, List.not_mem_nil, or_false] at hu
      subst hu
      simp only [ETRINV.Constraint.VarsLt] at hv
      simp only [ETRINV.Constraint.Holds] at hh
      obtain ⟨ha, hb, he⟩ := hv
      simp only [KindCons, recvVal, List.length_cons, List.length_nil]
      simp only [show 0 + 1 + 1 + 1 - 1 - 2 = 0 by rfl, show 0 + 1 + 1 + 1 - 1 - 1 = 1 by rfl,
        show 0 + 1 + 1 + 1 - 1 - 0 = 2 by rfl, List.getD_cons_zero, List.getD_cons_succ]
      rw [workVal_left (by omega), workVal_left (by omega), workVal_left (by omega)]
      rw [show e = 0 * n + e by ring, slotVal_low (by norm_num) he,
        show n + a = 1 * n + a by ring, slotVal_low (by norm_num) ha,
        slotVal_low (by norm_num) hb]
      linarith

end ArtGallery.Sec5.CoverT

end
