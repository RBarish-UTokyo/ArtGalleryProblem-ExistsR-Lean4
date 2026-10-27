module

public import ArtGallery.Hardness.BP.ConstraintKinds

/-!
# Boundary-point variant, constraints (iv)+(v): a guard set of size `g` on the boundary encodes a
solution

As `Sec5/ConstraintSide.lean` and `Sec5/ConstraintGlobal.lean`.  Let `G` be a set of guards on
the boundary of `polyCBP Φ n` (`n ≥ 1`) seeing the whole polygon, with `numGuardsBP Φ n` guards.
By the pinning statement (`Count.count_pinnedBP`) its guards are in bijection `e` with the
positions.  The base guard of slot `σ` lies on the floor of the bay of slot `σ`: it is
`(27σ/2 + t_σ, 0)` with `t_σ ∈ [0, 3/2]` (`baseOffBP`, `= 1/2` for slots with `one` spikes,
`base_guardBP`).

* `SideGBP`: the guards in the working frame of a side; `SideGBP.unitG`: they satisfy `UnitGBP`
  for every unit of the side.
* `sideRBP`, `sideLBP`: the guards in the working frames of the two sides satisfy `SideGBP` (the
  left side is the mirror image; its offsets are `3/2 − t_{4n−1−σ}`).
* The unit relations (`UnitGBP.orient_rel`, `ge_rel`, `le_rel`, `inv_rel`) give
  `t_{gn+i} + t_{3n+i} = 3/2` and, with `x_i = 1/2 + t_i`: `x_a + x_b = x_c`, `x_a x_b = 1`,
  `x_a = 1`.
* **`guardSet_solutionBP`**: there is `x` with `x_i ∈ [1/2, 2]`, `Φ` holds, and
  `(x_i + d_i, 0) ∈ G` for the Section 5 shift `d_i = shift i = 27i/2 − 1/2`.
* **`base_guard_uniqueBP`**: a guard of `G` on the base segment `s_σ` is the pinned guard of the
  base position `σ`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.BP.Constraint

open ArtGallery Set Polygon Sec5.Tmpl Vis.Cert
open ArtGallery.Sec5
open ArtGallery.Sec5.Corridor (Input place)
open ArtGallery.Sec5.Corridor.Input
open ArtGallery.Sec5.Count (unitBox baseSeg mirrorEquiv mirrorEquiv_apply
  mirrorEquiv_mirrorEquiv mainReg)
open ArtGallery.Sec5.Constraint (Foreign FarG far_of_mirror corridorBox_sub_unitBox mem_orientR
  mem_orientL mem_addR mem_addL mem_invR)
open ArtGallery.BP.Count (tsysOfBP uφBP GPosBP gPosSpotBP side_unitHypBP unitInputBP_S
  unitInputBP_H gPosSpotBP_main_eq gPosSpotBP_left_sg gPosSpotBP_left_tmpl count_pinnedBP
  filled_polyCBP_mirror sees_polyCBP_mirror gZBP_okOn gRegBP gRegBP_disjoint S_bigBP)

/-! ### The guards of a side -/

/-- **The guards of a side** (working frame, boundary-point variant). -/
structure SideGBP (Q : Polygon) (n k : ℕ) (us : List UnitSpec) (G : Set Point) (off : ℕ → ℝ)
    (tgs : (j : Fin us.length) → Fin (tsysOfBP (us[j]).kind).r → Point) : Prop where
  cov : ∀ z ∈ Q.filled, ∃ g ∈ G, Q.Sees g z
  off_mem : ∀ σ < 4 * n, 0 ≤ off σ ∧ off σ ≤ 3 / 2
  tg_mem : ∀ (j : Fin us.length) X,
    tgs j X ∈ uφBP n k j (us[j]) '' convexHull ℝ (intSet ((tsysOfBP (us[j]).kind).spot X))
  cls : ∀ g ∈ G, (∃ σ < 4 * n, g = (27 * (σ : ℝ) / 2 + off σ, 0)) ∨
    (∃ j : Fin us.length, (∃ kk < (unitInputBP n k j (us[j])).np,
        g = ratPoint ((unitInputBP n k j (us[j])).sgPt kk)) ∨ ∃ X, g = tgs j X) ∨
    FarG (S n k : ℝ) ((bigN n k : ℚ) : ℝ) g

section Side

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAtBP Q n k us st)
  {G : Set Point} {off : ℕ → ℝ}
  {tgs : (j : Fin us.length) → Fin (tsysOfBP (us[j]).kind).r → Point}
include hQ

/-- The positions of unit `j` lie in its unit box. -/
theorem unit_pos_boxBP (j : Fin us.length) {g : Point}
    (hg : (∃ kk < (unitInputBP n k j (us[j])).np,
        g = ratPoint ((unitInputBP n k j (us[j])).sgPt kk)) ∨
      ∃ X : Fin (tsysOfBP (us[j]).kind).r,
        g ∈ uφBP n k j (us[j]) '' convexHull ℝ (intSet ((tsysOfBP (us[j]).kind).spot X))) :
    g ∈ unitBox (S n k : ℝ) ((S n k : ℝ) + 3 * (j : ℕ) + 1) := by
  have hH := side_unitHypBP hQ j.2
  have e : unitBox (S n k : ℝ) ((S n k : ℝ) + 3 * (j : ℕ) + 1) =
      unitBox ((unitInputBP n k j (us[j])).S : ℝ) ((unitInputBP n k j (us[j])).H : ℝ) := by
    rw [unitInputBP_S, unitInputBP_H]
  rw [e]
  rcases hg with ⟨kk, hkk, rfl⟩ | ⟨X, x, hx, rfl⟩
  · exact corridorBox_sub_unitBox (hH.sg_corridor hkk)
  · exact (hH.phi_spot_box hx).2

/-- The positions of unit `j` lie in its unit box. -/
theorem SideGBP.pos_box (hS : SideGBP Q n k us G off tgs) (j : Fin us.length) {g : Point}
    (hg : (∃ kk < (unitInputBP n k j (us[j])).np,
        g = ratPoint ((unitInputBP n k j (us[j])).sgPt kk)) ∨ ∃ X, g = tgs j X) :
    g ∈ unitBox (S n k : ℝ) ((S n k : ℝ) + 3 * (j : ℕ) + 1) := by
  rcases hg with h | ⟨X, rfl⟩
  · exact unit_pos_boxBP hQ j (Or.inl h)
  · exact unit_pos_boxBP hQ j (Or.inr ⟨X, hS.tg_mem j X⟩)

/-- **Every unit of the side sees `UnitGBP` guards.** -/
theorem SideGBP.unitG (hS : SideGBP Q n k us G off tgs) {m : ℕ} (hm : m < us.length) :
    UnitGBP Q n k us m hm (us[m]'hm).kind G off (tgs ⟨m, hm⟩) := by
  refine ⟨rfl, hS.cov, hS.off_mem, hS.tg_mem ⟨m, hm⟩, fun g hg => ?_⟩
  have hSR := unitInputBP_S n k m (us[m]'hm)
  have hHR := unitInputBP_H n k m (us[m]'hm)
  rcases hS.cls g hg with hb | ⟨j, hj⟩ | hf
  · exact Or.inl hb
  · by_cases hjm : (j : ℕ) = m
    · have hj' : j = ⟨m, hm⟩ := Fin.ext hjm
      subst hj'
      rcases hj with hsg | hX
      · exact Or.inr (Or.inr (Or.inl hsg))
      · exact Or.inr (Or.inr (Or.inr hX))
    · refine Or.inr (Or.inl (Or.inl ⟨(S n k : ℝ) + 3 * (j : ℕ) + 1, ?_, ?_⟩))
      · rw [hHR]
        rcases lt_or_gt_of_ne hjm with h | h
        · left
          have : ((j : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast h
          linarith
        · right
          have : (m : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast h
          linarith
      · rw [hSR]; exact hS.pos_box hQ j hj
  · refine Or.inr (Or.inl (Or.inr ?_))
    rw [hSR]
    exact hf

end Side

/-! ### The base guards -/

section Global

variable {Φ : List ETRINV.Constraint} {n : ℕ} {G : Finset Point} (e : GPosBP Φ n ≃ G)

/-- The offset of the base guard of slot `σ`. -/
noncomputable def baseOffBP (σ : ℕ) : ℝ :=
  if h : σ < 4 * n then (e ⟨.inl (), ⟨σ, h⟩⟩ : Point).1 - 27 * (σ : ℝ) / 2 else 0

variable (he : ∀ X, (e X : Point) ∈ gPosSpotBP X ∧ ∀ q ∈ G, q ∈ gPosSpotBP X → q = e X)
include he

/-- **The base guards** lie on the floors of the bays of their slots. -/
theorem base_guardBP {σ : ℕ} (hσ : σ < 4 * n) :
    (e ⟨.inl (), ⟨σ, hσ⟩⟩ : Point) = (27 * (σ : ℝ) / 2 + baseOffBP e σ, 0) ∧
      0 ≤ baseOffBP e σ ∧ baseOffBP e σ ≤ 3 / 2 ∧
      (slotOne n Φ σ = true → baseOffBP e σ = 1 / 2) := by
  have h := (he ⟨.inl (), ⟨σ, hσ⟩⟩).1
  rw [gPosSpotBP_main_eq] at h
  have hx : ((slotX σ : ℚ) : ℝ) = 27 * (σ : ℝ) / 2 := by simp [slotX]
  simp only [baseOffBP, hσ, dite_true]
  by_cases h1 : slotOne n Φ σ = true
  · simp only [h1, ite_true] at h
    have h' : (e ⟨.inl (), ⟨σ, hσ⟩⟩ : Point) = ((slotX σ : ℝ) + 1 / 2, 0) := h
    rw [h', hx]
    refine ⟨by ext <;> simp, by norm_num, by norm_num, fun _ => by ring⟩
  · simp only [h1, Bool.false_eq_true, ite_false] at h
    obtain ⟨h2, h3, h4⟩ := h
    rw [hx] at h3 h4
    refine ⟨?_, by linarith, by linarith, fun h => absurd h h1⟩
    ext
    · simp only; ring
    · simp only; exact h2

end Global

/-- `108 n ≤ S`. -/
theorem S_ge_108 {Φ : List ETRINV.Constraint} {n : ℕ} : 108 * (n : ℝ) ≤ (S n (numC Φ) : ℝ) := by
  have h1 : ((100000 * bigN n (numC Φ) : ℕ) : ℝ) ≤ (S n (numC Φ) : ℝ) := by
    exact_mod_cast S_ge_mul_bigN
  have h2 : ((4 * n : ℕ) : ℝ) ≤ (bigN n (numC Φ) : ℝ) := by exact_mod_cast four_n_le_bigN
  push_cast at h1 h2
  have : (0 : ℝ) ≤ n := by positivity
  linarith

/-! ### The two sides -/

section Global2

variable {Φ : List ETRINV.Constraint} {n : ℕ} {G : Finset Point} (e : GPosBP Φ n ≃ G)
  (he : ∀ X, (e X : Point) ∈ gPosSpotBP X ∧ ∀ q ∈ G, q ∈ gPosSpotBP X → q = e X)
  (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n)
  (hcov : ∀ q ∈ (polyCBP Φ n).filled, ∃ g ∈ (G : Set Point), (polyCBP Φ n).Sees g q)
include he hΦ hn hcov

/-- **The guards in the frame of the right side.** -/
theorem sideRBP : SideGBP (polyCBP Φ n) n (numC Φ) (unitSpecs n Φ).1 (G : Set Point)
    (baseOffBP e) (fun j X => (e ⟨.inr (.inl j), .inr X⟩ : Point)) := by
  have hLs := leftSideBP hΦ hn
  have hSb' := S_ge_108 (Φ := Φ) (n := n)
  refine ⟨hcov, fun σ hσ => ?_, fun j X => (he ⟨.inr (.inl j), .inr X⟩).1, fun g hg => ?_⟩
  · obtain ⟨-, h1, h2, -⟩ := base_guardBP e he hσ; exact ⟨h1, h2⟩
  obtain ⟨⟨z, Y⟩, hY⟩ : ∃ Y, (e Y : Point) = g := ⟨e.symm ⟨g, hg⟩, by simp⟩
  rcases z with ⟨⟨⟩⟩ | j | j
  · rcases Y with ⟨σ, hσ⟩
    refine Or.inl ⟨σ, hσ, ?_⟩
    rw [← hY]; exact (base_guardBP e he hσ).1
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
      rw [gPosSpotBP_left_sg] at h
      obtain ⟨q, hq, hqe⟩ := h
      rw [← hY, ← hqe]
      exact far_of_mirror hSb' hjN (unit_pos_boxBP hLs j (Or.inl ⟨kk, kk.2, hq⟩))
    · have h := (he ⟨.inr (.inr j), .inr X⟩).1
      rw [gPosSpotBP_left_tmpl] at h
      obtain ⟨q, hq, hqe⟩ := h
      rw [← hY, ← hqe]
      exact far_of_mirror hSb' hjN (unit_pos_boxBP hLs j (Or.inr ⟨X, hq⟩))

/-- **The guards in the frame of the left side** (mirror image). -/
theorem sideLBP : SideGBP (polyMBP Φ n) n (numC Φ) (unitSpecs n Φ).2
    (mirrorEquiv n '' (G : Set Point)) (fun σ => 3 / 2 - baseOffBP e (4 * n - 1 - σ))
    (fun j X => mirrorEquiv n (e ⟨.inr (.inr j), .inr X⟩ : Point)) := by
  have hR := rightSideBP hΦ hn
  have hSb' := S_ge_108 (Φ := Φ) (n := n)
  refine ⟨fun z hz => ?_, fun σ hσ => ?_, fun j X => ?_, fun g' hg' => ?_⟩
  · have hz' : mirrorEquiv n z ∈ (polyCBP Φ n).filled := by
      rw [filled_polyCBP_mirror]; exact ⟨z, hz, rfl⟩
    obtain ⟨g, hgG, hgs⟩ := hcov _ hz'
    refine ⟨mirrorEquiv n g, ⟨g, hgG, rfl⟩, ?_⟩
    rw [← sees_polyCBP_mirror, mirrorEquiv_mirrorEquiv]; exact hgs
  · obtain ⟨-, h1, h2, -⟩ := base_guardBP e he (σ := 4 * n - 1 - σ) (by omega)
    constructor <;> linarith
  · have h := (he ⟨.inr (.inr j), .inr X⟩).1
    rw [gPosSpotBP_left_tmpl] at h
    obtain ⟨q, hq, hqe⟩ := h
    rw [← hqe, mirrorEquiv_mirrorEquiv]; exact hq
  obtain ⟨g, hg, rfl⟩ := hg'
  obtain ⟨⟨z, Y⟩, hY⟩ : ∃ Y, (e Y : Point) = g := ⟨e.symm ⟨g, hg⟩, by simp⟩
  rcases z with ⟨⟨⟩⟩ | j | j
  · rcases Y with ⟨σ, hσ⟩
    refine Or.inl ⟨4 * n - 1 - σ, by omega, ?_⟩
    rw [← hY, (base_guardBP e he hσ).1, mirrorEquiv_apply,
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
    refine far_of_mirror hSb' hjN (unit_pos_boxBP hR j ?_)
    rcases Y with kk | X
    · exact Or.inl ⟨kk, kk.2, (he ⟨.inr (.inl j), .inl kk⟩).1⟩
    · exact Or.inr ⟨X, (he ⟨.inr (.inl j), .inr X⟩).1⟩
  · refine Or.inr (Or.inl ⟨j, ?_⟩)
    rcases Y with kk | X
    · left
      refine ⟨kk, kk.2, ?_⟩
      have h := (he ⟨.inr (.inr j), .inl kk⟩).1
      rw [gPosSpotBP_left_sg] at h
      obtain ⟨q, hq, hqe⟩ := h
      rw [← hY, ← hqe, mirrorEquiv_mirrorEquiv]; exact hq
    · right; exact ⟨X, by rw [← hY]⟩

end Global2

/-! ### The relations of the units of a side -/

section Rel

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAtBP Q n k us st)
  {G : Set Point} {off : ℕ → ℝ}
  {tgs : (j : Fin us.length) → Fin (tsysOfBP (us[j]).kind).r → Point}
  (hS : SideGBP Q n k us G off tgs)
include hQ hS

omit hQ hS in
/-- Changing the kind of `UnitGBP` along an equality. -/
theorem UnitGBP.retype {m : ℕ} {hm : m < us.length} {κ κ' : Kind}
    {tg : Fin (tsysOfBP κ).r → Point}
    (hU : UnitGBP Q n k us m hm κ G off tg) (h : κ = κ') :
    ∃ tg' : Fin (tsysOfBP κ').r → Point, UnitGBP Q n k us m hm κ' G off tg' := by
  subst h; exact ⟨tg, hU⟩

/-- The unit `u` of the side with the guards of the side. -/
theorem SideGBP.unitG_of {u : UnitSpec} (hu : u ∈ us) :
    ∃ m, ∃ hm : m < us.length, us[m] = u ∧ ∃ tg : Fin (tsysOfBP u.kind).r → Point,
      UnitGBP Q n k us m hm u.kind G off tg := by
  obtain ⟨m, hm, hus⟩ := List.mem_iff_getElem.1 hu
  obtain ⟨tg, hU⟩ := (hS.unitG hQ hm).retype (κ' := u.kind) (by rw [hus])
  exact ⟨m, hm, hus, tg, hU⟩

omit hQ hS in
/-- The working slots of a unit with known spec. -/
theorem sigma_eqBP {m : ℕ} {hm : m < us.length} {u : UnitSpec} (hus : us[m] = u) (j : ℕ) :
    (unitInputBP n k m (us[m]'hm)).sigma j = u.work.getD j 0 := by
  rw [hus]; rfl

/-- An orientation unit of the side. -/
theorem SideGBP.orient_of {u : UnitSpec} (hu : u ∈ us) (hk : u.kind = .orient) :
    5 / 2 ≤ (1 / 2 + off (u.work.getD 0 0)) + (1 / 2 + off (u.work.getD 1 0)) := by
  obtain ⟨m, hm, hus, tg, hU⟩ := hS.unitG_of hQ hu
  obtain ⟨tg', hU'⟩ := hU.retype hk
  have := hU'.orient_rel hQ hm
  rwa [sigma_eqBP hus, sigma_eqBP hus] at this

/-- A `≥`-add unit of the side. -/
theorem SideGBP.ge_of {u : UnitSpec} (hu : u ∈ us) (hk : u.kind = .ge) :
    1 / 2 + off (u.work.getD 2 0) ≤
      (1 / 2 + off (u.work.getD 0 0)) + (1 / 2 + off (u.work.getD 1 0)) := by
  obtain ⟨m, hm, hus, tg, hU⟩ := hS.unitG_of hQ hu
  obtain ⟨tg', hU'⟩ := hU.retype hk
  have := hU'.ge_rel hQ hm
  rwa [sigma_eqBP hus, sigma_eqBP hus, sigma_eqBP hus] at this

/-- A `≤`-add unit of the side. -/
theorem SideGBP.le_of {u : UnitSpec} (hu : u ∈ us) (hk : u.kind = .le) :
    1 / 2 + off (u.work.getD 2 0) + 5 / 2 ≤
      (1 / 2 + off (u.work.getD 0 0)) + (1 / 2 + off (u.work.getD 1 0)) := by
  obtain ⟨m, hm, hus, tg, hU⟩ := hS.unitG_of hQ hu
  obtain ⟨tg', hU'⟩ := hU.retype hk
  have := hU'.le_rel hQ hm
  rwa [sigma_eqBP hus, sigma_eqBP hus, sigma_eqBP hus] at this

/-- An inversion unit of the side. -/
theorem SideGBP.inv_of {u : UnitSpec} (hu : u ∈ us) (hk : u.kind = .inv) :
    (1 / 2 + off (u.work.getD 0 0)) * (2 - off (u.work.getD 1 0)) = 1 := by
  obtain ⟨m, hm, hus, tg, hU⟩ := hS.unitG_of hQ hu
  obtain ⟨tg', hU'⟩ := hU.retype hk
  have := hU'.inv_rel hQ hm
  rwa [sigma_eqBP hus, sigma_eqBP hus] at this

end Rel

/-! ### Facts (iv) and (v) -/

/-- **A set of `numGuardsBP Φ n` guards on the boundary seeing the polygon encodes a solution.**
For `n ≥ 1`, every set `G` of guards on the boundary of `polyCBP Φ n` that sees the whole polygon
with `G.card = numGuardsBP Φ n` yields an assignment `x` with values in `[1/2, 2]` solving `Φ`,
such that `G` contains the guard `(x_i + d_i, 0)` of the representative slot `i` of every variable,
where `d_i = shift i = 27i/2 − 1/2`. -/
theorem guardSet_solutionBP {Φ : List ETRINV.Constraint} {n : ℕ} (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    (hn : 0 < n) (G : Finset Point) (hGΩ : (G : Set Point) ⊆ (polyCBP Φ n).boundary)
    (hcov : ∀ q ∈ (polyCBP Φ n).filled, ∃ g ∈ (G : Set Point), (polyCBP Φ n).Sees g q)
    (hcard : G.card = numGuardsBP Φ n) :
    ∃ x : ℕ → ℝ, (∀ i < n, 1 / 2 ≤ x i ∧ x i ≤ 2) ∧ (∀ c ∈ Φ, c.Holds x) ∧
      ∀ i < n, (x i + ((shift i : ℚ) : ℝ), (0 : ℝ)) ∈ G := by
  obtain ⟨e, he⟩ := count_pinnedBP hΦ hn G hGΩ hcov hcard
  have hR := sideRBP e he hΦ hn hcov
  have hL := sideLBP e he hΦ hn hcov
  have hRs := rightSideBP hΦ hn
  have hLs := leftSideBP hΦ hn
  set t := baseOffBP e with ht
  have tmem : ∀ σ < 4 * n, 0 ≤ t σ ∧ t σ ≤ 3 / 2 := fun σ hσ =>
    ⟨(base_guardBP e he hσ).2.1, (base_guardBP e he hσ).2.2.1⟩
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
      have h1 : t a = 1 / 2 := (base_guardBP e he (σ := a) (by omega)).2.2.2 hone
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
    have hb := (base_guardBP e he (σ := i) (by omega)).1
    rw [hb] at hg
    convert hg using 2
    simp only [shift]; push_cast; ring

/-! ### Uniqueness of the guard on a base segment -/

/-- Distinct base segments are disjoint. -/
theorem baseSeg_disjointBP {σ τ : ℕ} (h : σ ≠ τ) : Disjoint (baseSeg σ) (baseSeg τ) := by
  rw [Set.disjoint_left]
  rintro p ⟨-, h1, h2⟩ ⟨-, h3, h4⟩
  simp only [slotX] at h1 h2 h3 h4
  push_cast at h1 h2 h3 h4
  rcases lt_or_gt_of_ne h with h' | h'
  · have : (σ : ℝ) + 1 ≤ τ := by exact_mod_cast h'
    linarith
  · have : (τ : ℝ) + 1 ≤ σ := by exact_mod_cast h'
    linarith

/-- The base segment of a slot lies in the region of the main area. -/
theorem baseSeg_mainRegBP {Φ : List ETRINV.Constraint} {n σ : ℕ} (hσ : σ < 4 * n) :
    baseSeg σ ⊆ gRegBP Φ n (.inl ()) := by
  rintro p ⟨-, h1, h2⟩
  have hS := S_bigBP (n := n) (Φ := Φ)
  have hσ' : (σ : ℝ) + 1 ≤ 4 * n := by exact_mod_cast hσ
  have h0 : (0 : ℝ) ≤ σ := by positivity
  simp only [slotX] at h1 h2
  push_cast at h1 h2
  simp only [gRegBP, mainReg, Set.mem_ofPred_eq]
  constructor <;> linarith

/-- The position of a base slot lies on its base segment. -/
theorem gPosSpotBP_main_sub {Φ : List ETRINV.Constraint} {n : ℕ} (σ : Fin (4 * n)) :
    gPosSpotBP (⟨.inl (), σ⟩ : GPosBP Φ n) ⊆ baseSeg σ := by
  rw [gPosSpotBP_main_eq]
  split_ifs
  · rintro p rfl
    simp only [baseSeg, Set.mem_ofPred_eq]
    norm_num
  · exact le_rfl

/-- **The guard on a base segment is unique**: in a set of `numGuardsBP Φ n` guards on the
boundary seeing the polygon (pinned by `count_pinnedBP`), a guard on the base segment `s_σ` is the
guard of the base position `σ`. -/
theorem base_guard_uniqueBP {Φ : List ETRINV.Constraint} {n : ℕ} (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    (hn : 0 < n) {G : Finset Point} (e : GPosBP Φ n ≃ G)
    (he : ∀ X, (e X : Point) ∈ gPosSpotBP X ∧ ∀ q ∈ G, q ∈ gPosSpotBP X → q = e X)
    (σ : Fin (4 * n)) {p : Point} (hpG : p ∈ G) (hp : p ∈ baseSeg σ) :
    p = e ⟨.inl (), σ⟩ := by
  obtain ⟨⟨z, Y⟩, hY⟩ := e.surjective ⟨p, hpG⟩
  have hpY : p ∈ gPosSpotBP (⟨z, Y⟩ : GPosBP Φ n) := by
    have := (he ⟨z, Y⟩).1
    rwa [hY] at this
  rcases z with _ | j | j
  · change Fin (4 * n) at Y
    by_cases hYσ : Y = σ
    · subst hYσ
      rw [hY]
    · exfalso
      have hne : (Y : ℕ) ≠ σ := fun h => hYσ (Fin.ext h)
      exact Set.disjoint_left.1 (baseSeg_disjointBP hne) (gPosSpotBP_main_sub Y hpY) hp
  · exfalso
    have h1 := (gZBP_okOn hΦ hn (.inr (.inl j))).spot_reg Y hpY
    have h2 := baseSeg_mainRegBP (Φ := Φ) σ.2 hp
    exact Set.disjoint_left.1 (gRegBP_disjoint _ _ (by simp)) h2 h1
  · exfalso
    have h1 := (gZBP_okOn hΦ hn (.inr (.inr j))).spot_reg Y hpY
    have h2 := baseSeg_mainRegBP (Φ := Φ) σ.2 hp
    exact Set.disjoint_left.1 (gRegBP_disjoint _ _ (by simp)) h2 h1

/-- The representative guard `(x_i + d_i, 0)` of a value `x_i ∈ [1/2, 2]` lies on the base
segment `s_i`. -/
theorem shift_mem_baseSegBP {i : ℕ} {v : ℝ} (hv : 1 / 2 ≤ v ∧ v ≤ 2) :
    (v + ((shift i : ℚ) : ℝ), (0 : ℝ)) ∈ baseSeg i := by
  refine ⟨rfl, ?_, ?_⟩ <;> simp only [slotX, shift] <;> push_cast <;> linarith [hv.1, hv.2]

end ArtGallery.BP.Constraint

end
