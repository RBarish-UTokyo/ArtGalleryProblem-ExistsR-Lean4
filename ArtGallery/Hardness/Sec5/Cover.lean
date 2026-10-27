module

public import ArtGallery.Hardness.Sec5.CoverRegion
public import ArtGallery.Hardness.Sec5.CoverCons

/-!
# Section 5, sufficiency (vi): the canonical guards see the whole polygon

**`canonGuards_guard`**: for `n ≥ 1`, variables `x_i ∈ [1/2, 2]` satisfying `Φ`, the canonical
guard set `canonGuards Φ n x` is a guard set of the global polygon `polyC Φ n`.

The region is the union of its pieces (`filled_eq_globU`), and each piece is seen:

* the main hexagon by the base guards (`hex_covered`);
* the pocket room of slot `σ` by the base guard of `σ` (`sees_pocket_room`; with `one` spikes the
  base guard is the value-`1` point);
* the region of a right unit by its base guards, corridor stationary guards and canonical
  template guards (`CoverU.unit_cover`): the receiver values of the unit are the values of the
  copied slots (`recvVal`), they satisfy the template constraint (`CoverT.right_cons`), and the
  base guards see the entrance on `x = S` (`base_sees_right`);
* the region of a left unit likewise in the mirrored polygon (`CoverT.left_cons`,
  `base_sees_left`); the mirror image of the base guard of working slot `w` is the base guard
  of slot `4n − 1 − w`.

The canonical points lie in the region (`canonPt_filled`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.Sec5.CoverM

open ArtGallery Set Polygon
open Corridor (Input CorridorAt c0 c1 d0 d1)
open Corridor.Input
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue ArtGallery.Sec5.Count

variable {Φ : List ETRINV.Constraint} {n : ℕ} {x : ℕ → ℝ}

/-! ### The base guards of a corridor -/

theorem umbra_p (I : Input) (j : ℕ) (t : ℝ) :
    (I.umbraR j).p t = (27 * (I.sigma j : ℝ) / 2 + t, 0) := by
  simp [umbraR, umbraQ, Corridor.copyPair, Corridor.CopyPair.castR, Corridor.CopyPair.p,
    Corridor.baseA]

theorem recv_tau (left : Bool) (k m : ℕ) (u : UnitSpec) {j : ℕ} (hj : j < u.work.length) :
    recvVal n x left u ((unitInput n k m u).tau j) = workVal n x left (u.work.getD j 0) := by
  have : u.work.length - 1 - (unitInput n k m u).tau j = j := by
    simp only [Corridor.Input.tau, Corridor.Input.np, unitInput]; omega
  simp only [recvVal, this]

theorem sigma_eq (k m : ℕ) (u : UnitSpec) (j : ℕ) :
    (unitInput n k m u).sigma j = u.work.getD j 0 := rfl

theorem slotX_real (σ : ℕ) : (slotX σ : ℝ) = 27 * (σ : ℝ) / 2 := by simp [slotX]

theorem work_mem {u : UnitSpec} {j : ℕ} (hj : j < u.work.length) : u.work.getD j 0 ∈ u.work := by
  rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj

/-! ### Canonical guards -/

theorem canon_base (hn : 0 < n) {σ : ℕ} (hσ : σ < 4 * n) : basePt n x σ ∈ canonGuards Φ n x := by
  classical
  have hn0 : n ≠ 0 := by omega
  simp only [canonGuards, hn0, ite_false, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨.inl (), (⟨σ, hσ⟩ : Fin (4 * n))⟩, rfl⟩

theorem canon_mem (hn : 0 < n) (X : GPos Φ n) : canonPt Φ n x X ∈ canonGuards Φ n x := by
  classical
  have hn0 : n ≠ 0 := by omega
  simp only [canonGuards, hn0, ite_false, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨X, rfl⟩

theorem base_mem (hn : 0 < n) (hx : ValsOK n x) (σ : ℕ) :
    (basePt n x σ).2 = 0 ∧ (slotX σ : ℝ) ≤ (basePt n x σ).1 ∧
      (basePt n x σ).1 ≤ slotX σ + 3 / 2 := by
  obtain ⟨h0, h1⟩ := slotVal_mem hn hx σ
  refine ⟨rfl, ?_, ?_⟩ <;> simp only [basePt] <;> linarith

section Main

variable (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) (hx : ValsOK n x) (hΦx : ∀ c ∈ Φ, c.Holds x)
include hΦ hn hx hΦx

theorem base_filled {σ : ℕ} (hσ : σ < 4 * n) : basePt n x σ ∈ (polyC Φ n).filled := by
  obtain ⟨b2, b1, b1'⟩ := base_mem hn hx σ
  have hs := sees_col hΦ hn hσ (g := basePt n x σ) (q := ((basePt n x σ).1, 1)) b2 b1 b1'
    (by linarith) (by linarith) le_rfl (by norm_num)
  exact hs (Geometry.left_mem_segment _ _)

/-- **The canonical points lie in the region.** -/
theorem canonPt_filled (X : GPos Φ n) : canonPt Φ n x X ∈ (polyC Φ n).filled := by
  have hv : ∀ (left : Bool) (u : UnitSpec), ∀ τ, 1 / 2 ≤ recvVal n x left u τ ∧
      recvVal n x left u τ ≤ 2 := fun left u τ => recvVal_mem hn hx left u τ
  -- the positions of a unit in the polygon of its side
  have hunit : ∀ {Q : Polygon} {us : List UnitSpec} {st : ℕ}, SideAt Q n (numC Φ) us st →
      ∀ (left : Bool) (i : Fin us.length) (X : UPos n (numC Φ) us i),
        unitPt n x left (numC Φ) i us[i] X ∈ Q.filled := by
    intro Q us st hQ left i X
    rcases X with j | X
    · have hg := hQ.good i.2
      exact CoverU.corG_subset hQ i.2 (hg.strip_subset j.2 (hg.sgPt_mem_strip j.2))
    · obtain ⟨hP', hL', hC', hS'⟩ := CoverU.tFrame hQ i.2
      have := CoverT.spot_subset hP' hL' hC' hS' X (tGuard_mem _ (hv left us[i]) X)
      rw [CoverU.tPoly, Hardening.Invariance.filled_mapPoly] at this
      obtain ⟨y, hy, hyx⟩ := this
      change uφ n (numC Φ) i us[i] (tGuard us[i].kind (recvVal n x left us[i]) X) ∈ Q.filled
      rw [← hyx]
      convert hy using 1
      exact AffineEquiv.apply_symm_apply _ _
  rcases X with ⟨_ | i | i, X⟩
  · exact base_filled hΦ hn hx hΦx (σ := ((show Fin (4 * n) from X) : ℕ))
      (show Fin (4 * n) from X).2
  · exact hunit (rightSide hΦ hn) false i X
  · rw [filled_polyC_mirror]
    exact ⟨_, hunit (leftSide hΦ hn) true i X, rfl⟩

/-! ### Coverage of the pieces -/

theorem hone {σ : ℕ} (h : slotOne n Φ σ = true) : (basePt n x σ).1 = slotX σ + 1 / 2 := by
  have hσ : σ < n := by
    simp only [slotOne, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1
  rw [basePt_eq_g1 σ hσ (holds_one hΦx h), g1Pt, absPt_eq]
  simp [g1Rel]

theorem pocket_covered {σ : ℕ} (hσ : σ < 4 * n) {z : Point} (hz : z ∈ pkU Φ n σ) :
    ∃ g ∈ canonGuards Φ n x, (polyC Φ n).Sees g z := by
  have hM := mainHyp hΦ hn
  obtain ⟨b2, b1, b1'⟩ := base_mem hn hx σ
  refine ⟨_, canon_base hn hσ, sees_pocket_room hM.simple hM.ccw (hM.pocket σ hσ)
    (boxSep hΦ hn hσ (T := 1) (by have := sS_big (Φ := Φ) (n := n); linarith)) b2 b1 b1'
    (hone hΦ hn hx hΦx) hz⟩

theorem right_covered (m : Fin (unitSpecs n Φ).1.length) {z : Point} (hz : z ∈ rU Φ n m) :
    ∃ g ∈ canonGuards Φ n x, (polyC Φ n).Sees g z := by
  have hQ := rightSide hΦ hn
  have hok : UnitOK n ((unitSpecs n Φ).1[m.1]'m.2) :=
    unitSpecs_ok hΦ _ (List.mem_append_left _ (List.getElem_mem _))
  have hv := fun τ => recvVal_mem hn hx false ((unitSpecs n Φ).1[m.1]'m.2) τ
  have hc := CoverT.right_cons hΦ hΦx _ (List.getElem_mem m.2)
  -- the base guard of pair `j` is the canonical base guard of its slot
  have hbase : ∀ j < (unitInput n (numC Φ) m ((unitSpecs n Φ).1[m.1]'m.2)).np,
      ((unitInput n (numC Φ) m ((unitSpecs n Φ).1[m.1]'m.2)).umbraR j).p
        (recvVal n x false ((unitSpecs n Φ).1[m.1]'m.2)
          ((unitInput n (numC Φ) m ((unitSpecs n Φ).1[m.1]'m.2)).tau j) - 1 / 2) =
        basePt n x (((unitSpecs n Φ).1[m.1]'m.2).work.getD j 0) := by
    intro j hj
    rw [umbra_p, recv_tau false _ _ _ hj, sigma_eq, CoverT.workVal_right, basePt, slotX_real]
  have hent : ∀ j < (unitInput n (numC Φ) m ((unitSpecs n Φ).1[m.1]'m.2)).np,
      ∀ w ∈ (unitInput n (numC Φ) m ((unitSpecs n Φ).1[m.1]'m.2)).entrance,
      (polyC Φ n).Sees (((unitInput n (numC Φ) m ((unitSpecs n Φ).1[m.1]'m.2)).umbraR j).p
        (recvVal n x false ((unitSpecs n Φ).1[m.1]'m.2)
          ((unitInput n (numC Φ) m ((unitSpecs n Φ).1[m.1]'m.2)).tau j) - 1 / 2)) w := by
    intro j hj w hw
    obtain ⟨e1, e2, e3⟩ := entrance_loc hQ m.2 hw
    rw [hbase j hj, show w = (sS Φ n, w.2) from Prod.ext e1 rfl]
    obtain ⟨b2, b1, b1'⟩ := base_mem hn hx (((unitSpecs n Φ).1[m.1]'m.2).work.getD j 0)
    exact base_sees_right hΦ hn (hok.lt _ (work_mem hj)) b2 b1 b1' (by linarith) e3.le
  rcases CoverU.unit_cover hQ m.2 hv hc hent z hz with ⟨j, hj, h⟩ | ⟨j, hj, h⟩ | ⟨X, h⟩
  · rw [hbase j hj] at h
    exact ⟨_, canon_base hn (hok.lt _ (work_mem hj)), h⟩
  · exact ⟨_, canon_mem hn ⟨.inr (.inl m), (.inl ⟨j, hj⟩ : UPos n (numC Φ) (unitSpecs n Φ).1 m)⟩,
      h⟩
  · exact ⟨_, canon_mem hn ⟨.inr (.inl m), (.inr X : UPos n (numC Φ) (unitSpecs n Φ).1 m)⟩, h⟩

theorem left_covered (m : Fin (unitSpecs n Φ).2.length) {z : Point} (hz : z ∈ lU Φ n m) :
    ∃ g ∈ canonGuards Φ n x, (polyC Φ n).Sees g z := by
  have hQ := leftSide hΦ hn
  have hok : UnitOK n ((unitSpecs n Φ).2[m.1]'m.2) :=
    unitSpecs_ok hΦ _ (List.mem_append_right _ (List.getElem_mem _))
  have hv := fun τ => recvVal_mem hn hx true ((unitSpecs n Φ).2[m.1]'m.2) τ
  have hc := CoverT.left_cons hΦ hΦx _ (List.getElem_mem m.2)
  rw [lU, mem_mirror_image] at hz
  -- the mirror image of the base guard of pair `j` is the canonical base guard of the slot
  -- `4n − 1 − w`
  have hbase : ∀ j < (unitInput n (numC Φ) m ((unitSpecs n Φ).2[m.1]'m.2)).np,
      mirrorEquiv n (((unitInput n (numC Φ) m ((unitSpecs n Φ).2[m.1]'m.2)).umbraR j).p
        (recvVal n x true ((unitSpecs n Φ).2[m.1]'m.2)
          ((unitInput n (numC Φ) m ((unitSpecs n Φ).2[m.1]'m.2)).tau j) - 1 / 2)) =
        basePt n x (4 * n - 1 - ((unitSpecs n Φ).2[m.1]'m.2).work.getD j 0) := by
    intro j hj
    have hw := hok.lt _ (work_mem hj)
    have hc : ((4 * n - 1 - ((unitSpecs n Φ).2[m.1]'m.2).work.getD j 0 : ℕ) : ℝ) =
        4 * n - 1 - (((unitSpecs n Φ).2[m.1]'m.2).work.getD j 0 : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [umbra_p, recv_tau true _ _ _ hj, sigma_eq, workVal, mirrorEquiv_apply, basePt,
      slotX_real, hc]
    simp only [ite_true]
    ext <;> simp only
    ring
  have hent : ∀ j < (unitInput n (numC Φ) m ((unitSpecs n Φ).2[m.1]'m.2)).np,
      ∀ w ∈ (unitInput n (numC Φ) m ((unitSpecs n Φ).2[m.1]'m.2)).entrance,
      (polyM Φ n).Sees (((unitInput n (numC Φ) m ((unitSpecs n Φ).2[m.1]'m.2)).umbraR j).p
        (recvVal n x true ((unitSpecs n Φ).2[m.1]'m.2)
          ((unitInput n (numC Φ) m ((unitSpecs n Φ).2[m.1]'m.2)).tau j) - 1 / 2)) w := by
    intro j hj w hw
    obtain ⟨e1, e2, e3⟩ := entrance_loc hQ m.2 hw
    rw [← sees_polyC_mirror, hbase j hj,
      show mirrorEquiv n w = (sXL Φ n, w.2) by rw [mirrorEquiv_apply, e1]; rfl]
    obtain ⟨b2, b1, b1'⟩ := base_mem hn hx (4 * n - 1 - ((unitSpecs n Φ).2[m.1]'m.2).work.getD j 0)
    exact base_sees_left hΦ hn (by omega) b2 b1 b1' (by linarith) e3.le
  have hmir : ∀ g : Point, (polyM Φ n).Sees g (mirrorEquiv n z) →
      (polyC Φ n).Sees (mirrorEquiv n g) z := fun g h => by
    rw [← sees_polyC_mirror, mirrorEquiv_mirrorEquiv] at h; exact h
  rcases CoverU.unit_cover hQ m.2 hv hc hent _ hz with ⟨j, hj, h⟩ | ⟨j, hj, h⟩ | ⟨X, h⟩
  · have h' := hmir _ h
    rw [hbase j hj] at h'
    exact ⟨_, canon_base hn (by omega), h'⟩
  · exact ⟨_, canon_mem hn ⟨.inr (.inr m), (.inl ⟨j, hj⟩ : UPos n (numC Φ) (unitSpecs n Φ).2 m)⟩,
      hmir _ h⟩
  · exact ⟨_, canon_mem hn ⟨.inr (.inr m), (.inr X : UPos n (numC Φ) (unitSpecs n Φ).2 m)⟩,
      hmir _ h⟩

end Main

end ArtGallery.Sec5.CoverM

namespace ArtGallery.Sec5

open ArtGallery CoverM

/-- **(vi) The canonical guards see the whole polygon**: for `n ≥ 1` and values
`x_i ∈ [1/2, 2]` satisfying `Φ`, `canonGuards Φ n x` is a guard set of `polyC Φ n`. -/
theorem canonGuards_guard {Φ : List ETRINV.Constraint} {n : ℕ} (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    (hn : 0 < n) {x : ℕ → ℝ} (hx : ∀ i < n, 1 / 2 ≤ x i ∧ x i ≤ 2)
    (hΦx : ∀ c ∈ Φ, c.Holds x) : (polyC Φ n).IsGuardSet (canonGuards Φ n x : Set Point) := by
  classical
  have hn0 : n ≠ 0 := by omega
  refine ⟨?_, ?_⟩
  · intro g hg
    simp only [canonGuards, hn0, ite_false, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_range] at hg
    obtain ⟨X, rfl⟩ := hg
    exact canonPt_filled hΦ hn hx hΦx X
  · intro z hz
    rw [filled_eq_globU hΦ hn] at hz
    rcases hz with (((h | h) | h) | h)
    · obtain ⟨σ, hσ, hs⟩ := hex_covered hΦ hn (basePt n x) (base_mem hn hx) z h
      exact ⟨_, canon_base hn hσ, hs⟩
    · obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 h
      exact pocket_covered hΦ hn hx hΦx σ.2 hσ
    · obtain ⟨m, hm⟩ := Set.mem_iUnion.1 h
      exact right_covered hΦ hn hx hΦx m hm
    · obtain ⟨m, hm⟩ := Set.mem_iUnion.1 h
      exact left_covered hΦ hn hx hΦx m hm

end ArtGallery.Sec5

end
