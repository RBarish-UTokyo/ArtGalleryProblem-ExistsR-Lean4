module

public import ArtGallery.Hardness.BP.CoverGlob

/-!
# Boundary-point variant, coverage: the region of the global polygon is the union of its pieces

As `Sec5/CoverRegion.lean`.  `filled_eq_globU`: the region of `polyCBP Φ n` is the union of the
main hexagon, the pocket rooms with bays, the right unit regions and the mirrored left unit
regions.  By the frontier criterion (`Polygon.filled_eq_of_frontier_subset`) it suffices that
every point of the union off the boundary is an interior point of the union (`globU_interior`):
away from the doors this is the room property of each piece (`pocketBP_isRoom`,
`CoverU.unitU_interior`); at an open door (a pocket mouth on `y = 1`, a unit entrance on `x = S` or
on `x = X_L`) the two half-discs lie in the two adjacent pieces.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.BP.CoverM

open ArtGallery Set Polygon Filter Topology ArtGallery.Sec5
open ArtGallery.Sec5.CoverM (hexSet sS sTop sXL pwR pvR ptR ptL pvL pwL sS_big sS_lt_sTop sTop_eq
  mem_mirror_image mem_hex_of ev_lt ev_gt hex_strict_right hex_strict_left hex_ev_right
  hex_ev_left hex_ev_bottom hex_ev_inner bottom_hex slot_of_bottom continuous_mirrorEquiv
  seg_bounds slotX_real_nonneg slotX_add_le_real vtx_mem_bdry)
open ArtGallery.Sec5.Count (mirrorEquiv mirrorEquiv_apply mirrorEquiv_mirrorEquiv)
open ArtGallery.Sec5.Corridor (CorridorAt c0 c1 d0 d1)
open ArtGallery.Sec5.Corridor.Input
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

variable {Φ : List ETRINV.Constraint} {n : ℕ}

/-! ### The entrances -/

/-- **The entrances lie on `x = S`**, strictly between `y = S` and the top. -/
theorem entrance_loc {Q : Polygon} {us : List UnitSpec} {st m : ℕ}
    (hQ : SideAtBP Q n (numC Φ) us st) (hm : m < us.length) {y : Point}
    (hy : y ∈ (unitInputBP n (numC Φ) m (us[m]'hm)).entrance) :
    y.1 = sS Φ n ∧ sS Φ n + 1 ≤ y.2 ∧ y.2 < sTop Φ n := by
  have hS : 54 * (n : ℝ) + 100000 ≤ (S n (numC Φ) : ℝ) := sS_big
  have hρ0 := (hQ.good hm).rhoR_pos
  have hρ : (unitInputBP n (numC Φ) m (us[m]'hm)).rhoR < 1 / 100 := by
    rw [rhoR_eq, hQ.cast_S hm, div_lt_iff₀ (by linarith)]; linarith
  have hlen := hQ.len
  have hmN : (m : ℝ) + 1 ≤ bigN n (numC Φ) := by
    exact_mod_cast (show m + 1 ≤ bigN n (numC Φ) by omega)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [Corridor.Input.entrance, ratPoint_d0', ratPoint_c0', hQ.cast_S hm, hQ.cast_H hm] at hy
  obtain ⟨b1, b2, b3, b4⟩ := seg_bounds hy
  simp only [min_self, max_self] at b1 b2
  rw [sTop_eq]
  simp only [sS]
  refine ⟨le_antisymm b2 b1, le_trans (le_min ?_ ?_) b3, lt_of_le_of_lt b4 (max_lt ?_ ?_)⟩
  · simp only; linarith
  · simp only; linarith
  · simp only; linarith
  · simp only; linarith

/-! ### The pieces in the union -/

theorem hex_in_globU : hexSet Φ n ⊆ globU Φ n := fun _ h => Or.inl (Or.inl (Or.inl h))

theorem pk_in_globU {σ : ℕ} (hσ : σ < 4 * n) : pkU Φ n σ ⊆ globU Φ n :=
  fun _ h => Or.inl (Or.inl (Or.inr (mem_iUnion.2 ⟨⟨σ, hσ⟩, h⟩)))

theorem rU_in_globU (m : Fin (unitSpecs n Φ).1.length) : rU Φ n m ⊆ globU Φ n :=
  fun _ h => Or.inl (Or.inr (mem_iUnion.2 ⟨m, h⟩))

theorem lU_in_globU (m : Fin (unitSpecs n Φ).2.length) : lU Φ n m ⊆ globU Φ n :=
  fun _ h => Or.inr (mem_iUnion.2 ⟨m, h⟩)

theorem door_hex {σ : ℕ} (hσ : σ < 4 * n) {y : Point}
    (hy : y ∈ ArtGallery.segment (ratPoint (mR σ)) (ratPoint (mL σ))) : y ∈ hexSet Φ n := by
  rw [ratPoint_mR_BP, ratPoint_mL_BP] at hy
  obtain ⟨b1, b2, b3, b4⟩ := seg_bounds hy
  simp only [min_self, max_self] at b3 b4
  have ha := slotX_real_nonneg σ
  have hb := slotX_add_le_real (n := n) hσ
  refine bottom_hex (le_antisymm b4 b3) ?_ ?_
  · exact le_trans (le_min (by linarith) (by linarith)) b1
  · exact le_trans b2 (max_le (by linarith) (by linarith))

/-! ### Interior points of the union -/

section Global

variable (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n)
include hΦ hn

theorem mL_bdry {σ : ℕ} (hσ : σ < 4 * n) : ratPoint (mL σ) ∈ (polyCBP Φ n).boundary := by
  have hM := mainHypBP hΦ hn
  have h := (hM.pocket σ hσ) 0 (Nat.zero_le _)
  have hP : 0 < (polyCBP Φ n).n := by have := hM.simple.1; omega
  rw [← pocketBPClosed_getD_zero (slotOne n Φ σ) σ, ← h]
  exact vtx_mem_bdry (Nat.mod_lt _ hP)

theorem mR_bdry {σ : ℕ} (hσ : σ < 4 * n) : ratPoint (mR σ) ∈ (polyCBP Φ n).boundary := by
  have hM := mainHypBP hΦ hn
  have h := (hM.pocket σ hσ) ((bayRel (slotOne n Φ σ)).length + 1) le_rfl
  have hP : 0 < (polyCBP Φ n).n := by have := hM.simple.1; omega
  rw [← pocketBPClosed_getD_last (slotOne n Φ σ) σ, ← h]
  exact vtx_mem_bdry (Nat.mod_lt _ hP)

/-- **An open pocket mouth is interior to the union.** -/
theorem bottom_local {y : Point} (hy1 : y.2 = 1) (hx1 : -6 ≤ y.1) (hx2 : y.1 ≤ 54 * n - 6)
    (hyb : y ∉ (polyCBP Φ n).boundary) : ∀ᶠ z in 𝓝 y, z ∈ globU Φ n := by
  obtain ⟨σ, hσ, a1, a2⟩ := slot_of_bottom hΦ hn hx1 hx2
  rcases a1.lt_or_eq with a1 | a1
  swap
  · exfalso; apply hyb
    rw [show y = ratPoint (mL σ) by rw [ratPoint_mL_BP]; exact Prod.ext a1.symm hy1]
    exact mL_bdry hΦ hn hσ
  rcases a2.lt_or_eq with a2 | a2
  swap
  · exfalso; apply hyb
    rw [show y = ratPoint (mR σ) by rw [ratPoint_mR_BP]; exact Prod.ext a2 hy1]
    exact mR_bdry hΦ hn hσ
  have ha := slotX_real_nonneg σ
  have hb := slotX_add_le_real (n := n) hσ
  filter_upwards [pocketBP_below (slotOne n Φ σ) σ hy1 a1 a2,
    hex_ev_bottom (Φ := Φ) hy1 (by linarith) (by linarith)] with z h1 h2
  rcases le_total z.2 1 with h | h
  · exact pk_in_globU hσ (h1 h)
  · exact hex_in_globU (h2 h)

theorem mirror_not_bdry {y : Point} (hyb : y ∉ (polyCBP Φ n).boundary) :
    mirrorEquiv n y ∉ (polyMBP Φ n).boundary := by
  intro h
  rw [polyM_bdry hn] at h
  obtain ⟨b, hb, hbe⟩ := h
  have : b = y := (mirrorEquiv n).injective hbe
  exact hyb (this ▸ hb)

/-- **The hexagon points off the boundary are interior to the union.** -/
theorem hex_local {y : Point} (hy : y ∈ hexSet Φ n) (hyb : y ∉ (polyCBP Φ n).boundary) :
    ∀ᶠ z in 𝓝 y, z ∈ globU Φ n := by
  have hS := sS_big (Φ := Φ) (n := n)
  have hT := sS_lt_sTop (Φ := Φ) (n := n)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hX : sXL Φ n ≤ -100012 := by simp only [sXL]; linarith
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hy
  rcases d1.lt_or_eq with d1 | d1
  swap
  · exfalso; apply hyb; apply diagR_bdry hn
    obtain ⟨t, rfl⟩ := CoverU.exists_lerp_of_det_zero (a := pwR n) (b := pvR Φ n)
      (fun h => by have := congrArg Prod.snd h; simp only [pwR, pvR] at this; linarith) d1.symm
    simp only [Geometry.lerp, pwR, pvR] at d3 d6
    exact Geometry.lerp_mem_segment _ _ (by nlinarith) (by nlinarith)
  rcases d2.lt_or_eq with d2 | d2
  swap
  · exfalso; apply hyb; apply diagL_bdry hn
    obtain ⟨t, rfl⟩ := CoverU.exists_lerp_of_det_zero (a := pvL Φ n) (b := pwL)
      (fun h => by have := congrArg Prod.snd h; simp only [pvL, pwL] at this; linarith) d2.symm
    simp only [Geometry.lerp, pvL, pwL] at d3 d5
    exact Geometry.lerp_mem_segment _ _ (by nlinarith) (by nlinarith)
  rcases d4.lt_or_eq with d4 | d4
  swap
  · exfalso; apply hyb; apply top_bdry hn
    have hd : 0 < sS Φ n - sXL Φ n := by linarith
    refine ⟨(sS Φ n - y.1) / (sS Φ n - sXL Φ n), div_nonneg (by linarith) hd.le,
      (div_le_one hd).2 (by linarith), ?_⟩
    simp only [ptR, ptL]
    ext
    · simp only; field_simp; ring
    · simp only; rw [d4]; ring
  rcases d3.lt_or_eq with d3 | d3
  swap
  · have hy1 : y.2 = 1 := d3.symm
    refine bottom_local hΦ hn hy1 ?_ ?_ hyb
    · simp only [det, pvL, pwL, sXL] at d2; rw [hy1] at d2; nlinarith
    · simp only [det, pwR, pvR] at d1; rw [hy1] at d1; nlinarith
  rcases d6.lt_or_eq with d6 | d6
  swap
  · -- the right entrance
    have hy2 : sS Φ n < y.2 := by
      simp only [det, pwR, pvR] at d1; rw [d6] at d1; nlinarith
    have hyy : y = (sS Φ n, y.2) := Prod.ext d6 rfl
    rcases right_vertical hn hΦ hy2.le d4.le with h | ⟨m, hm, h⟩
    · exact absurd (hyy ▸ h) hyb
    rw [← hyy] at h
    have hQ := rightSideBP hΦ hn
    obtain ⟨e1, e2, e3⟩ := entrance_loc hQ hm h
    obtain ⟨r, hr, hc⟩ := CoverU.entrance_halfball hQ hm h hyb
    have hc' : ∀ᶠ z in 𝓝 y, sS Φ n ≤ z.1 → z ∈ rU Φ n ⟨m, hm⟩ :=
      Metric.eventually_nhds_iff.2 ⟨r, hr, fun z hz h' =>
        Or.inl (Or.inl (hc z hz (by rw [hQ.cast_S hm]; exact h')))⟩
    filter_upwards [hex_ev_right e1 e2 e3, hc'] with z h1 h2
    rcases le_total z.1 (sS Φ n) with h | h
    · exact hex_in_globU (h1 h)
    · exact rU_in_globU _ (h2 h)
  rcases d5.lt_or_eq with d5 | d5
  swap
  · -- the left entrance
    have hy2 : sS Φ n < y.2 := by
      simp only [det, pvL, pwL] at d2; rw [← d5] at d2; nlinarith
    have hyy : mirrorEquiv n y = (sS Φ n, y.2) := by
      rw [mirrorEquiv_apply, ← d5]; simp only [sXL]; ext <;> simp
    have hyb' := mirror_not_bdry hΦ hn hyb
    rw [hyy] at hyb'
    rcases left_vertical hn hΦ hy2.le d4.le with h | ⟨m, hm, h⟩
    · exact absurd h hyb'
    have hQ := leftSideBP hΦ hn
    obtain ⟨e1, e2, e3⟩ := entrance_loc hQ hm h
    obtain ⟨r, hr, hc⟩ := CoverU.entrance_halfball hQ hm h hyb'
    have hev : ∀ᶠ z in 𝓝 y, dist (mirrorEquiv n z) (sS Φ n, y.2) < r := by
      rw [← hyy]
      exact (continuous_mirrorEquiv.tendsto y).eventually (Metric.ball_mem_nhds _ hr)
    have hc' : ∀ᶠ z in 𝓝 y, z.1 ≤ sXL Φ n → z ∈ lU Φ n ⟨m, hm⟩ := by
      filter_upwards [hev] with z hz h'
      rw [lU, mem_mirror_image]
      refine Or.inl (Or.inl (hc _ hz ?_))
      rw [hQ.cast_S hm, mirrorEquiv_apply]
      simp only [sXL] at h'
      change sS Φ n ≤ _
      linarith
    filter_upwards [hex_ev_left d5.symm e2 e3, hc'] with z h1 h2
    rcases le_total z.1 (sXL Φ n) with h | h
    · exact lU_in_globU _ (h2 h)
    · exact hex_in_globU (h1 h)
  filter_upwards [hex_ev_inner d1 d2 d3 d4 d5 d6] with z hz
  exact hex_in_globU hz

theorem pocket_local {σ : ℕ} (hσ : σ < 4 * n) {y : Point} (hy : y ∈ pkU Φ n σ)
    (hyb : y ∉ (polyCBP Φ n).boundary) : ∀ᶠ z in 𝓝 y, z ∈ globU Φ n := by
  by_cases hD : y ∈ ArtGallery.segment (ratPoint (mR σ)) (ratPoint (mL σ))
  · exact hex_local hΦ hn (door_hex hσ hD) hyb
  have hM := mainHypBP hΦ hn
  have hyP := pkU_subset hΦ hn hσ hy
  obtain ⟨-, hR⟩ := pocketBP_isRoom hM.simple hM.ccw (hM.pocket σ hσ)
  obtain ⟨ε, hε, h⟩ := hR y hy hyP hD
  have hopen := (Jordan.isOpen_filled_sdiff_boundary hM.simple).mem_nhds ⟨hyP, hyb⟩
  filter_upwards [hopen, Metric.ball_mem_nhds y hε] with z hz hz'
  exact pk_in_globU hσ (h z hz.1 hz')

theorem rU_local (m : Fin (unitSpecs n Φ).1.length) {y : Point} (hy : y ∈ rU Φ n m)
    (hyb : y ∉ (polyCBP Φ n).boundary) : ∀ᶠ z in 𝓝 y, z ∈ globU Φ n := by
  have hQ := rightSideBP hΦ hn
  by_cases he : y ∈ (unitInputBP n (numC Φ) m ((unitSpecs n Φ).1[m.1]'m.2)).entrance
  · obtain ⟨e1, e2, e3⟩ := entrance_loc hQ m.2 he
    obtain ⟨a1, a2, a3, a4⟩ := hex_strict_right e1 e2
    exact hex_local hΦ hn (mem_hex_of a1.le a2.le a3.le e3.le a4.le e1.le) hyb
  · exact Filter.mem_of_superset
      (mem_interior_iff_mem_nhds.1 (CoverU.unitU_interior hQ m.2 hy hyb he)) (rU_in_globU m)

theorem lU_local (m : Fin (unitSpecs n Φ).2.length) {y : Point} (hy : y ∈ lU Φ n m)
    (hyb : y ∉ (polyCBP Φ n).boundary) : ∀ᶠ z in 𝓝 y, z ∈ globU Φ n := by
  have hQ := leftSideBP hΦ hn
  rw [lU, mem_mirror_image] at hy
  have hyb' := mirror_not_bdry hΦ hn hyb
  by_cases he : mirrorEquiv n y ∈
      (unitInputBP n (numC Φ) m ((unitSpecs n Φ).2[m.1]'m.2)).entrance
  · obtain ⟨e1, e2, e3⟩ := entrance_loc hQ m.2 he
    rw [mirrorEquiv_apply] at e1 e2 e3
    simp only at e1 e2 e3
    have e1' : y.1 = sXL Φ n := by simp only [sXL]; linarith
    obtain ⟨a1, a2, a3, a4⟩ := hex_strict_left e1' e2
    exact hex_local hΦ hn (mem_hex_of a1.le a2.le a3.le e3.le e1'.ge a4.le) hyb
  · have hi := mem_interior_iff_mem_nhds.1 (CoverU.unitU_interior hQ m.2 hy hyb' he)
    have := (continuous_mirrorEquiv.tendsto y).eventually hi
    filter_upwards [this] with z hz
    exact lU_in_globU m (mem_mirror_image.2 hz)

/-- **Every point of the union off the boundary is an interior point of the union.** -/
theorem globU_interior {y : Point} (hy : y ∈ globU Φ n) (hyb : y ∉ (polyCBP Φ n).boundary) :
    y ∈ interior (globU Φ n) := by
  rw [mem_interior_iff_mem_nhds]
  rcases hy with (((h | h) | h) | h)
  · exact hex_local hΦ hn h hyb
  · obtain ⟨σ, hσ⟩ := mem_iUnion.1 h
    exact pocket_local hΦ hn σ.2 hσ hyb
  · obtain ⟨m, hm⟩ := mem_iUnion.1 h
    exact rU_local hΦ hn m hm hyb
  · obtain ⟨m, hm⟩ := mem_iUnion.1 h
    exact lU_local hΦ hn m hm hyb

theorem frontier_globU : frontier (globU Φ n) ⊆ (polyCBP Φ n).boundary := by
  intro y hy
  by_contra hyb
  exact hy.2 (globU_interior hΦ hn (isClosed_globU.frontier_subset hy) hyb)

/-- **The region of the global polygon is the union of its pieces.** -/
theorem filled_eq_globU : (polyCBP Φ n).filled = globU Φ n := by
  have hS := sS_big (Φ := Φ) (n := n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN2 : (2 : ℝ) ≤ bigN n (numC Φ) := by exact_mod_cast two_le_bigN
  have k : 0 < det (pwR n) (pvR Φ n) ((1 : ℝ) / 2, (3 : ℝ) / 2) ∧
      0 < det (pvL Φ n) pwL ((1 : ℝ) / 2, (3 : ℝ) / 2) ∧ (1 : ℝ) < 3 / 2 ∧
      (3 : ℝ) / 2 < sTop Φ n ∧ sXL Φ n < 1 / 2 ∧ (1 : ℝ) / 2 < sS Φ n := by
    simp only [det, pwR, pvR, pvL, pwL, sXL, sTop]
    refine ⟨by nlinarith, by nlinarith, by norm_num, by linarith, by linarith, by linarith⟩
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := k
  refine Polygon.filled_eq_of_frontier_subset (mainHypBP hΦ hn).simple isClosed_globU
    (bdry_subset_globU hΦ hn) (frontier_globU hΦ hn) (globU_subset hΦ hn)
    ⟨((1 : ℝ) / 2, (3 : ℝ) / 2), hex_in_globU (mem_hex_of k1.le k2.le k3.le k4.le k5.le k6.le),
      strict_not_bdryBP hΦ hn k1 k2 k3 k4 k5 k6⟩

end Global

end ArtGallery.BP.CoverM

end
