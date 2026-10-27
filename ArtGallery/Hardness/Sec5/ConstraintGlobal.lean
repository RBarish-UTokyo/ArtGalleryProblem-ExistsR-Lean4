module

public import ArtGallery.Hardness.Sec5.ConstraintSide

/-!
# Section 5, constraints (iv)+(v): a guard set of size `g` encodes a solution

Let `G` be a guard set of `polyC Φ n` with `numGuards Φ n` guards (`n ≥ 1`).  By the pinning
statement (`Count.count_pinned`) its guards are in bijection `e` with the positions.  The base guard
of slot `σ` is `(27σ/2 + t_σ, 0)` with `t_σ ∈ [0, 3/2]` (`baseOff`, `= 1/2` for slots with `one`
spikes).

* `sideR`, `sideL`: the guards in the working frames of the two sides satisfy `SideG` (the left
  side is the mirror image; its offsets are `3/2 − t_{4n−1−σ}`).
* The unit relations (`UnitG.orient_rel`, `ge_rel`, `le_rel`, `inv_rel`) for the units of
  `unitSpecs` give `t_{gn+i} + t_{3n+i} = 3/2` (orientation units of both sides), and with
  `x_i = 1/2 + t_i`: `x_a + x_b = x_c`, `x_a x_b = 1`, `x_a = 1`.
* **`guardSet_solution`** (facts (iv)+(v) of `08_proof_plan.md` §1): there is `x` with
  `x_i ∈ [1/2, 2]`, `Φ` holds, and `(x_i + d_i, 0) ∈ G` for the shift `d_i = shift i = 27i/2 − 1/2`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.Sec5.Constraint

open ArtGallery Set Polygon Tmpl Vis.Cert
open Corridor (Input place)
open Corridor.Input
open ArtGallery.Sec5.Count (tsysOf uφ unitBox GPos gPosSpot mirrorEquiv Zone ZPos)

section Global

variable {Φ : List ETRINV.Constraint} {n : ℕ} {G : Finset Point} (e : GPos Φ n ≃ G)

/-- The offset of the base guard of slot `σ`. -/
noncomputable def baseOff (σ : ℕ) : ℝ :=
  if h : σ < 4 * n then (e ⟨.inl (), ⟨σ, h⟩⟩ : Point).1 - 27 * (σ : ℝ) / 2 else 0

variable (he : ∀ X, (e X : Point) ∈ gPosSpot X ∧ ∀ q ∈ G, q ∈ gPosSpot X → q = e X)
include he

/-- **The base guards.** -/
theorem base_guard {σ : ℕ} (hσ : σ < 4 * n) :
    (e ⟨.inl (), ⟨σ, hσ⟩⟩ : Point) = (27 * (σ : ℝ) / 2 + baseOff e σ, 0) ∧
      0 ≤ baseOff e σ ∧ baseOff e σ ≤ 3 / 2 ∧ (slotOne n Φ σ = true → baseOff e σ = 1 / 2) := by
  have h := (he ⟨.inl (), ⟨σ, hσ⟩⟩).1
  rw [Count.gPosSpot_main] at h
  have hx : ((slotX σ : ℚ) : ℝ) = 27 * (σ : ℝ) / 2 := by simp [slotX]
  simp only [baseOff, hσ, dite_true]
  by_cases h1 : slotOne n Φ σ = true
  · simp only [h1, ite_true] at h
    have h' : (e ⟨.inl (), ⟨σ, hσ⟩⟩ : Point) = g1Pt σ := h
    rw [h', g1Pt, absPt_eq, hx]
    simp only [g1Rel]
    push_cast
    refine ⟨by ext <;> simp, by norm_num, by norm_num, fun _ => by ring⟩
  · simp only [h1, Bool.false_eq_true, ite_false] at h
    obtain ⟨h2, h3, h4⟩ := h
    rw [hx] at h3 h4
    refine ⟨?_, by linarith, by linarith, fun h => absurd h h1⟩
    ext
    · simp only; ring
    · simp only; exact h2

end Global

/-- A mirrored point of a unit box lies in the far region. -/
theorem far_of_mirror {n k j : ℕ} (hS' : 108 * (n : ℝ) ≤ (S n k : ℝ)) (hj : j < bigN n k)
    {q : Point} (hq : q ∈ unitBox (S n k : ℝ) ((S n k : ℝ) + 3 * (j : ℕ) + 1)) :
    FarG (S n k : ℝ) ((bigN n k : ℚ) : ℝ) (mirrorEquiv n q) := by
  obtain ⟨b1, b2, b3, b4⟩ := hq
  have hj' : (j : ℝ) + 1 ≤ (bigN n k : ℝ) := by exact_mod_cast hj
  have hn0 : (0 : ℝ) ≤ n := by positivity
  rw [Count.mirrorEquiv_apply]
  refine ⟨?_, ?_, ?_⟩ <;> simp only <;> push_cast <;> linarith

section Global2

variable {Φ : List ETRINV.Constraint} {n : ℕ} {G : Finset Point} (e : GPos Φ n ≃ G)
  (he : ∀ X, (e X : Point) ∈ gPosSpot X ∧ ∀ q ∈ G, q ∈ gPosSpot X → q = e X)
  (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) (hG : (polyC Φ n).IsGuardSet (G : Set Point))
include he hΦ hn hG

/-- **The guards in the frame of the right side.** -/
theorem sideR : SideG (polyC Φ n) n (numC Φ) (unitSpecs n Φ).1 (G : Set Point) (baseOff e)
    (fun j X => (e ⟨.inr (.inl j), .inr X⟩ : Point)) := by
  have hR := rightSide hΦ hn
  have hLs := leftSide hΦ hn
  have hSb' : 108 * (n : ℝ) ≤ (S n (numC Φ) : ℝ) := by
    have h1 : ((100000 * bigN n (numC Φ) : ℕ) : ℝ) ≤ (S n (numC Φ) : ℝ) := by
      exact_mod_cast S_ge_mul_bigN
    have h2 : ((4 * n : ℕ) : ℝ) ≤ (bigN n (numC Φ) : ℝ) := by exact_mod_cast four_n_le_bigN
    push_cast at h1 h2
    have : (0 : ℝ) ≤ n := by positivity
    linarith
  refine ⟨hG.2, fun σ hσ => ?_, fun j X => (he ⟨.inr (.inl j), .inr X⟩).1, fun g hg => ?_⟩
  · obtain ⟨-, h1, h2, -⟩ := base_guard e he hσ; exact ⟨h1, h2⟩
  obtain ⟨⟨z, Y⟩, hY⟩ : ∃ Y, (e Y : Point) = g := ⟨e.symm ⟨g, hg⟩, by simp⟩
  rcases z with ⟨⟨⟩⟩ | j | j
  · rcases Y with ⟨σ, hσ⟩
    refine Or.inl ⟨σ, hσ, ?_⟩
    rw [← hY]; exact (base_guard e he hσ).1
  · refine Or.inr (Or.inl ⟨j, ?_⟩)
    rcases Y with kk | X
    · left
      refine ⟨kk, kk.2, ?_⟩
      rw [← hY]; exact (he ⟨.inr (.inl j), .inl kk⟩).1
    · right; exact ⟨X, hY.symm⟩
  · refine Or.inr (Or.inr ?_)
    have hjN : (j : ℕ) < bigN n (numC Φ) := lt_of_lt_of_le j.2 (length_unitSpecs_snd n Φ)
    rcases Y with kk | X
    · have h := (he ⟨.inr (.inr j), .inl kk⟩).1
      rw [Count.gPosSpot_left_sg] at h
      obtain ⟨q, hq, hqe⟩ := h
      rw [← hY, ← hqe]
      exact far_of_mirror hSb' hjN (unit_pos_box hLs j (Or.inl ⟨kk, kk.2, hq⟩))
    · have h := (he ⟨.inr (.inr j), .inr X⟩).1
      rw [Count.gPosSpot_left_tmpl] at h
      obtain ⟨q, hq, hqe⟩ := h
      rw [← hY, ← hqe]
      exact far_of_mirror hSb' hjN (unit_pos_box hLs j (Or.inr ⟨X, hq⟩))

/-- **The guards in the frame of the left side** (mirror image). -/
theorem sideL : SideG (polyM Φ n) n (numC Φ) (unitSpecs n Φ).2 (mirrorEquiv n '' (G : Set Point))
    (fun σ => 3 / 2 - baseOff e (4 * n - 1 - σ))
    (fun j X => mirrorEquiv n (e ⟨.inr (.inr j), .inr X⟩ : Point)) := by
  have hR := rightSide hΦ hn
  have hSb' : 108 * (n : ℝ) ≤ (S n (numC Φ) : ℝ) := by
    have h1 : ((100000 * bigN n (numC Φ) : ℕ) : ℝ) ≤ (S n (numC Φ) : ℝ) := by
      exact_mod_cast S_ge_mul_bigN
    have h2 : ((4 * n : ℕ) : ℝ) ≤ (bigN n (numC Φ) : ℝ) := by exact_mod_cast four_n_le_bigN
    push_cast at h1 h2
    have : (0 : ℝ) ≤ n := by positivity
    linarith
  refine ⟨fun z hz => ?_, fun σ hσ => ?_, fun j X => ?_, fun g' hg' => ?_⟩
  · have hz' : mirrorEquiv n z ∈ (polyC Φ n).filled := by
      rw [Count.filled_polyC_mirror]; exact ⟨z, hz, rfl⟩
    obtain ⟨g, hgG, hgs⟩ := hG.2 _ hz'
    refine ⟨mirrorEquiv n g, ⟨g, hgG, rfl⟩, ?_⟩
    rw [← Count.sees_polyC_mirror, Count.mirrorEquiv_mirrorEquiv]; exact hgs
  · obtain ⟨-, h1, h2, -⟩ := base_guard e he (σ := 4 * n - 1 - σ) (by omega)
    constructor <;> linarith
  · have h := (he ⟨.inr (.inr j), .inr X⟩).1
    rw [Count.gPosSpot_left_tmpl] at h
    obtain ⟨q, hq, hqe⟩ := h
    rw [← hqe, Count.mirrorEquiv_mirrorEquiv]; exact hq
  obtain ⟨g, hg, rfl⟩ := hg'
  obtain ⟨⟨z, Y⟩, hY⟩ : ∃ Y, (e Y : Point) = g := ⟨e.symm ⟨g, hg⟩, by simp⟩
  rcases z with ⟨⟨⟩⟩ | j | j
  · rcases Y with ⟨σ, hσ⟩
    refine Or.inl ⟨4 * n - 1 - σ, by omega, ?_⟩
    rw [← hY, (base_guard e he hσ).1, Count.mirrorEquiv_apply,
      show 4 * n - 1 - (4 * n - 1 - σ) = σ by omega]
    have hc : ((4 * n - 1 - σ : ℕ) : ℝ) = 4 * (n : ℝ) - 1 - σ := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [hc]
    ext
    · simp only; ring
    · simp
  · refine Or.inr (Or.inr ?_)
    have hjN : (j : ℕ) < bigN n (numC Φ) := lt_of_lt_of_le j.2 (length_unitSpecs_fst n Φ)
    rw [← hY]
    refine far_of_mirror hSb' hjN (unit_pos_box hR j ?_)
    rcases Y with kk | X
    · exact Or.inl ⟨kk, kk.2, (he ⟨.inr (.inl j), .inl kk⟩).1⟩
    · exact Or.inr ⟨X, (he ⟨.inr (.inl j), .inr X⟩).1⟩
  · refine Or.inr (Or.inl ⟨j, ?_⟩)
    rcases Y with kk | X
    · left
      refine ⟨kk, kk.2, ?_⟩
      have h := (he ⟨.inr (.inr j), .inl kk⟩).1
      rw [Count.gPosSpot_left_sg] at h
      obtain ⟨q, hq, hqe⟩ := h
      rw [← hY, ← hqe, Count.mirrorEquiv_mirrorEquiv]; exact hq
    · right; exact ⟨X, by rw [← hY]⟩

end Global2

/-! ### The relations of the units of a side -/

section Rel

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAt Q n k us st)
  {G : Set Point} {off : ℕ → ℝ}
  {tgs : (j : Fin us.length) → Fin (tsysOf (us[j]).kind).r → Point}
  (hS : SideG Q n k us G off tgs)
include hQ hS

omit hQ hS in
/-- Changing the kind of `UnitG` along an equality. -/
theorem UnitG.retype {m : ℕ} {hm : m < us.length} {κ κ' : Kind} {tg : Fin (tsysOf κ).r → Point}
    (hU : UnitG Q n k us m hm κ G off tg) (h : κ = κ') :
    ∃ tg' : Fin (tsysOf κ').r → Point, UnitG Q n k us m hm κ' G off tg' := by
  subst h; exact ⟨tg, hU⟩

/-- The unit `u` of the side with the guards of the side. -/
theorem SideG.unitG_of {u : UnitSpec} (hu : u ∈ us) :
    ∃ m, ∃ hm : m < us.length, us[m] = u ∧ ∃ tg : Fin (tsysOf u.kind).r → Point,
      UnitG Q n k us m hm u.kind G off tg := by
  obtain ⟨m, hm, hus⟩ := List.mem_iff_getElem.1 hu
  obtain ⟨tg, hU⟩ := (hS.unitG hQ hm).retype (κ' := u.kind) (by rw [hus])
  exact ⟨m, hm, hus, tg, hU⟩

omit hQ hS in
/-- The working slots of a unit with known spec. -/
theorem sigma_eq {m : ℕ} {hm : m < us.length} {u : UnitSpec} (hus : us[m] = u) (j : ℕ) :
    (unitInput n k m (us[m]'hm)).sigma j = u.work.getD j 0 := by
  rw [hus]; rfl

/-- An orientation unit of the side. -/
theorem SideG.orient_of {u : UnitSpec} (hu : u ∈ us) (hk : u.kind = .orient) :
    5 / 2 ≤ (1 / 2 + off (u.work.getD 0 0)) + (1 / 2 + off (u.work.getD 1 0)) := by
  obtain ⟨m, hm, hus, tg, hU⟩ := hS.unitG_of hQ hu
  obtain ⟨tg', hU'⟩ := hU.retype hk
  have := hU'.orient_rel hQ hm
  rwa [sigma_eq hus, sigma_eq hus] at this

/-- A `≥`-add unit of the side. -/
theorem SideG.ge_of {u : UnitSpec} (hu : u ∈ us) (hk : u.kind = .ge) :
    1 / 2 + off (u.work.getD 2 0) ≤ (1 / 2 + off (u.work.getD 0 0)) + (1 / 2 + off (u.work.getD 1 0)) := by
  obtain ⟨m, hm, hus, tg, hU⟩ := hS.unitG_of hQ hu
  obtain ⟨tg', hU'⟩ := hU.retype hk
  have := hU'.ge_rel hQ hm
  rwa [sigma_eq hus, sigma_eq hus, sigma_eq hus] at this

/-- A `≤`-add unit of the side. -/
theorem SideG.le_of {u : UnitSpec} (hu : u ∈ us) (hk : u.kind = .le) :
    1 / 2 + off (u.work.getD 2 0) + 5 / 2 ≤
      (1 / 2 + off (u.work.getD 0 0)) + (1 / 2 + off (u.work.getD 1 0)) := by
  obtain ⟨m, hm, hus, tg, hU⟩ := hS.unitG_of hQ hu
  obtain ⟨tg', hU'⟩ := hU.retype hk
  have := hU'.le_rel hQ hm
  rwa [sigma_eq hus, sigma_eq hus, sigma_eq hus] at this

/-- An inversion unit of the side. -/
theorem SideG.inv_of {u : UnitSpec} (hu : u ∈ us) (hk : u.kind = .inv) :
    (1 / 2 + off (u.work.getD 0 0)) * (2 - off (u.work.getD 1 0)) = 1 := by
  obtain ⟨m, hm, hus, tg, hU⟩ := hS.unitG_of hQ hu
  obtain ⟨tg', hU'⟩ := hU.retype hk
  have := hU'.inv_rel hQ hm
  rwa [sigma_eq hus, sigma_eq hus] at this

end Rel

/-! ### The units of the construction -/

/-- The right orientation units are units of the right side. -/
theorem mem_orientR {n i g : ℕ} {Φ : List ETRINV.Constraint} (hi : i < n) (hg : g < 3) :
    (⟨.orient, [g * n + i, 3 * n + i], [g * n + i, 3 * n + i]⟩ : UnitSpec) ∈ (unitSpecs n Φ).1 := by
  simp only [unitSpecs, List.mem_append, orientR, List.mem_flatMap, List.mem_range, List.mem_map]
  exact Or.inl (Or.inl ⟨i, hi, g, hg, rfl⟩)

/-- The left orientation units are units of the left side. -/
theorem mem_orientL {n i g : ℕ} {Φ : List ETRINV.Constraint} (hi : i < n) (hg : g < 3) :
    (⟨.orient, [3 * n + i, g * n + i], [workSlot n (3 * n + i), workSlot n (g * n + i)]⟩ :
      UnitSpec) ∈ (unitSpecs n Φ).2 := by
  simp only [unitSpecs, List.mem_append, orientL, List.mem_flatMap, List.mem_range, List.mem_map]
  exact Or.inl ⟨i, hi, g, hg, rfl⟩

/-- An addition constraint has a `≥`-add unit on the right side. -/
theorem mem_addR {n a b c : ℕ} {Φ : List ETRINV.Constraint} (h : ETRINV.Constraint.add a b c ∈ Φ) :
    (⟨.ge, [a, n + b, 2 * n + c], [a, n + b, 2 * n + c]⟩ : UnitSpec) ∈ (unitSpecs n Φ).1 := by
  simp only [unitSpecs, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inr ⟨_, h, by simp [addR]⟩)

/-- An addition constraint has a `≤`-add unit on the left side. -/
theorem mem_addL {n a b c : ℕ} {Φ : List ETRINV.Constraint} (h : ETRINV.Constraint.add a b c ∈ Φ) :
    (⟨.le, [2 * n + b, n + a, c], [workSlot n (2 * n + b), workSlot n (n + a), workSlot n c]⟩ :
      UnitSpec) ∈ (unitSpecs n Φ).2 := by
  simp only [unitSpecs, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨_, h, by simp [addL]⟩

/-- An inversion constraint has an inversion unit on the right side. -/
theorem mem_invR {n a b : ℕ} {Φ : List ETRINV.Constraint} (h : ETRINV.Constraint.inv a b ∈ Φ) :
    (⟨.inv, [a, 3 * n + b], [a, 3 * n + b]⟩ : UnitSpec) ∈ (unitSpecs n Φ).1 := by
  simp only [unitSpecs, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨_, h, by simp [invR]⟩

/-! ### Facts (iv) and (v) -/

/-- **A guard set with `numGuards Φ n` guards encodes a solution** (facts (iv)+(v) of
`08_proof_plan.md` §1).  For `n ≥ 1`, every guard set `G` of `polyC Φ n` with
`G.card = numGuards Φ n` yields an assignment `x` with values in `[1/2, 2]` solving `Φ`, such that
`G` contains the guard `(x_i + d_i, 0)` of the representative slot `i` of every variable, where
`d_i = shift i = 27i/2 − 1/2`. -/
theorem guardSet_solution {Φ : List ETRINV.Constraint} {n : ℕ} (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    (hn : 0 < n) (G : Finset Point) (hG : (polyC Φ n).IsGuardSet (G : Set Point))
    (hcard : G.card = numGuards Φ n) :
    ∃ x : ℕ → ℝ, (∀ i < n, 1 / 2 ≤ x i ∧ x i ≤ 2) ∧ (∀ c ∈ Φ, c.Holds x) ∧
      ∀ i < n, (x i + ((shift i : ℚ) : ℝ), (0 : ℝ)) ∈ G := by
  obtain ⟨e, he⟩ := Count.count_pinned hΦ hn G hG hcard
  have hR := sideR e he hΦ hn hG
  have hL := sideL e he hΦ hn hG
  have hRs := rightSide hΦ hn
  have hLs := leftSide hΦ hn
  set t := baseOff e with ht
  have tmem : ∀ σ < 4 * n, 0 ≤ t σ ∧ t σ ≤ 3 / 2 := fun σ hσ =>
    ⟨(base_guard e he hσ).2.1, (base_guard e he hσ).2.2.1⟩
  have hws : ∀ σ < 4 * n, 4 * n - 1 - workSlot n σ = σ := fun σ hσ => by
    simp only [workSlot]; omega
  -- the orientation units: all four copies of a variable carry the same value
  have horient : ∀ i < n, ∀ g < 3, t (g * n + i) + t (3 * n + i) = 3 / 2 := by
    intro i hi g hg
    have h1 := hR.orient_of hRs (mem_orientR (Φ := Φ) hi hg) rfl
    have h2 := hL.orient_of hLs (mem_orientL (Φ := Φ) hi hg) rfl
    simp only [List.getD_cons_zero, List.getD_cons_succ] at h1 h2
    rw [hws _ (by omega), hws _ (by nlinarith)] at h2
    linarith
  have hcopy : ∀ i < n, ∀ g < 3, t (g * n + i) = t i := by
    intro i hi g hg
    have := horient i hi g hg
    have := horient i hi 0 (by norm_num)
    simp only [zero_mul, zero_add] at this
    linarith
  have hneg : ∀ i < n, t (3 * n + i) = 3 / 2 - t i := by
    intro i hi
    have := horient i hi 0 (by norm_num)
    simp only [zero_mul, zero_add] at this
    linarith
  refine ⟨fun i => 1 / 2 + t i, fun i hi => ?_, fun c hc => ?_, fun i hi => ?_⟩
  · obtain ⟨h1, h2⟩ := tmem i (by omega)
    constructor <;> linarith
  · have hc' := hΦ c hc
    cases c with
    | one a =>
      simp only [ETRINV.Constraint.VarsLt] at hc'
      have hone : slotOne n Φ a = true := by
        simp only [slotOne, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
        exact ⟨hc', _, hc, by simp [isOneOf]⟩
      simp only [ETRINV.Constraint.Holds]
      have h1 : t a = 1 / 2 := (base_guard e he (σ := a) (by omega)).2.2.2 hone
      rw [h1]; norm_num
    | add a b c =>
      simp only [ETRINV.Constraint.VarsLt] at hc'
      obtain ⟨ha, hb, hcc⟩ := hc'
      have h1 := hR.ge_of hRs (mem_addR (n := n) hc) rfl
      have h2 := hL.le_of hLs (mem_addL (n := n) hc) rfl
      simp only [List.getD_cons_zero, List.getD_cons_succ] at h1 h2
      rw [hws _ (by omega), hws _ (by omega), hws _ (by omega)] at h2
      have e1 := hcopy b hb 1 (by norm_num)
      have e2 := hcopy c hcc 2 (by norm_num)
      have e3 := hcopy a ha 1 (by norm_num)
      have e4 := hcopy b hb 2 (by norm_num)
      simp only [one_mul] at e1 e3
      simp only [ETRINV.Constraint.Holds]
      linarith
    | inv a b =>
      simp only [ETRINV.Constraint.VarsLt] at hc'
      obtain ⟨ha, hb⟩ := hc'
      have h1 := hR.inv_of hRs (mem_invR (n := n) hc) rfl
      simp only [List.getD_cons_zero, List.getD_cons_succ] at h1
      rw [hneg b hb] at h1
      simp only [ETRINV.Constraint.Holds]
      linarith
  · have hg := (e ⟨.inl (), ⟨i, by omega⟩⟩).2
    have hb := (base_guard e he (σ := i) (by omega)).1
    rw [hb] at hg
    convert hg using 2
    simp only [shift]; push_cast; ring

end ArtGallery.Sec5.Constraint

end
