module

public import ArtGallery.Hardness.BP.CoverUnit

/-!
# Boundary-point variant, coverage: the unit region is a room with the entrance as door

As `Sec5/CoverUnitLocal.lean`.  For unit `m` of a side `SideAtBP Q n k us st`, the unit region
`unitU = corG ∪ chanG ∪ tkG` (corridor, channel, template room):

* contains the unit chain (`unitChain_subset`);
* every point of `unitU` off the boundary of `Q` and off the entrance is an interior point of
  `unitU` (`unitU_interior`): inside a piece by the room property of the corridor (doors window
  and entrance) and of the template room (door the mouth); on the window the corridor and the
  channel are the two closed half-planes; on the mouth the template room and the channel;
* near a point of the open entrance, the closed half-plane `x ≥ S` lies in the corridor
  (`entrance_halfball`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.BP.CoverU

open ArtGallery Set Polygon Vis.Cert Sec5.Tmpl ArtGallery.Sec5 CoverK
open ArtGallery.Sec5.CoverT (ChanD RecvD chanSet Corners corners_of_B chanB_parts
  interior_chanSet mem_interior_chanSet convex_chanSet isClosed_chanSet)
open ArtGallery.Sec5.CoverU (exists_lerp_of_det_zero chan_side0 chan_side1 chan_side2 chan_side3
  mem_interior_of_halves eventually_pos continuous_det chan_halfball)
open ArtGallery.BP.Count (uφBP unitS_geBP)
open ArtGallery.Sec5.Corridor (CorridorAt c0 c1 d0 d1)
open ArtGallery.Sec5.Corridor.Input
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

/-! ### Vertices and walls of the unit in `Q` -/

section Unit

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAtBP Q n k us st)
  {m : ℕ} (hm : m < us.length)
include hQ hm

theorem unitChain_len : (unitChainBP n k m (us[m]'hm)).length =
    (unitInputBP n k m (us[m]'hm)).chainBefore.length + (tmplVBP (us[m]'hm).kind).length +
      (unitInputBP n k m (us[m]'hm)).chainAfter.length := by
  simp [unitChainBP, placedTmplBP, Nat.add_assoc]

theorem cb_pos : 2 ≤ (unitInputBP n k m (us[m]'hm)).chainBefore.length := by
  simp [chainBefore]

theorem ca_pos : 2 ≤ (unitInputBP n k m (us[m]'hm)).chainAfter.length := by
  simp [chainAfter]

theorem vtx_c1 : Q.vtx (hQ.tStart hm - 1) =
    ratPoint (c1 (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H) := by
  have hl := unitChain_len hQ hm
  have hcb := cb_pos hQ hm
  have e : hQ.tStart hm - 1 = unitStartBP n k us st m +
      ((unitInputBP n k m (us[m]'hm)).chainBefore.length - 1) := by
    simp only [SideAtBP.tStart]; omega
  rw [e, hQ.vtx m hm _ (by omega)]
  congr 1
  simp only [unitChainBP, List.append_assoc]
  rw [List.getD_append _ _ _ _ (by omega), chainBefore_getD_last]

theorem vtx_d1 : Q.vtx (hQ.tStart hm + (tmplVBP (us[m]'hm).kind).length) =
    ratPoint (d1 (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H) := by
  have hl := unitChain_len hQ hm
  have hca := ca_pos hQ hm
  have e : hQ.tStart hm + (tmplVBP (us[m]'hm).kind).length = unitStartBP n k us st m +
      ((unitInputBP n k m (us[m]'hm)).chainBefore.length + (tmplVBP (us[m]'hm).kind).length) := by
    simp only [SideAtBP.tStart]; omega
  rw [e, hQ.vtx m hm _ (by omega)]
  congr 1
  have hlp : (placedTmplBP (unitInputBP n k m (us[m]'hm)) (us[m]'hm).kind).length =
      (tmplVBP (us[m]'hm).kind).length := by simp [placedTmplBP]
  simp only [unitChainBP]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_append, hlp, Nat.sub_self, chainAfter_getD_zero]

theorem vtx_t (j : ℕ) (hj : j < (tmplVBP (us[m]'hm).kind).length) :
    Q.vtx (hQ.tStart hm + j) = uφBP n k m (us[m]'hm) (intPoint (cv (tmplVBP (us[m]'hm).kind) j)) :=
  hQ.tmpl_vtx hm j hj

theorem tStart_lt : hQ.tStart hm + (tmplVBP (us[m]'hm).kind).length < Q.n := by
  have h := hQ.end_le hm
  have hl := unitChain_len hQ hm
  have hca := ca_pos hQ hm
  simp only [SideAtBP.tStart]; omega

theorem tStart_pos : 1 ≤ hQ.tStart hm := by
  have hcb := cb_pos hQ hm
  simp only [SideAtBP.tStart]; omega

/-- The lower channel wall is an edge of `Q`. -/
theorem lowerWall_bdry : ArtGallery.segment (ratPoint (c1 (unitInputBP n k m (us[m]'hm)).S
    (unitInputBP n k m (us[m]'hm)).H)) (uφBP n k m (us[m]'hm) (intPoint (cv (tmplVBP (us[m]'hm).kind) 0)))
    ⊆ Q.boundary := by
  intro p hp
  have h1 := tStart_lt hQ hm
  have h0 := tStart_pos hQ hm
  refine ⟨hQ.tStart hm - 1, by omega, ?_⟩
  rw [Polygon.edge, vtx_c1 hQ hm, show (hQ.tStart hm - 1 + 1) % Q.n = hQ.tStart hm + 0 by
    rw [Nat.mod_eq_of_lt (by omega)]; omega, vtx_t hQ hm 0 (by have := tmplBP_length (us[m]'hm).kind; omega)]
  exact hp

/-- The upper channel wall is an edge of `Q`. -/
theorem upperWall_bdry : ArtGallery.segment (uφBP n k m (us[m]'hm) (intPoint (cv (tmplVBP (us[m]'hm).kind)
    ((tmplVBP (us[m]'hm).kind).length - 1))))
    (ratPoint (d1 (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H)) ⊆ Q.boundary := by
  intro p hp
  have h1 := tStart_lt hQ hm
  have hl := tmplBP_length (us[m]'hm).kind
  refine ⟨hQ.tStart hm + ((tmplVBP (us[m]'hm).kind).length - 1), by omega, ?_⟩
  rw [Polygon.edge, vtx_t hQ hm _ (by omega), show (hQ.tStart hm + ((tmplVBP (us[m]'hm).kind).length - 1)
    + 1) % Q.n = hQ.tStart hm + (tmplVBP (us[m]'hm).kind).length by
    rw [Nat.mod_eq_of_lt (by omega)]; omega, vtx_d1 hQ hm]
  exact hp

/-! ### The pieces near their doors -/

omit hQ hm in
/-- An interior point of the region in a room, off the door, is an interior point of the room. -/
theorem interior_of_room {P : Polygon} (hP : P.Simple) {R D : Set Point} (hR : P.IsRoom R D)
    {y : Point} (hy : y ∈ R) (hyP : y ∈ P.filled) (hyb : y ∉ P.boundary) (hyD : y ∉ D) :
    y ∈ interior R := by
  obtain ⟨ε, hε, hR'⟩ := hR.2 y hy hyP hyD
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (Jordan.isOpen_filled_sdiff_boundary hP) y
    ⟨hyP, hyb⟩
  rw [mem_interior]
  refine ⟨Metric.ball y (min ε δ), fun z hz => ?_, Metric.isOpen_ball,
    Metric.mem_ball_self (lt_min hε hδ)⟩
  rw [Metric.mem_ball] at hz
  exact hR' z (hball (Metric.mem_ball.2 (lt_of_lt_of_le hz (min_le_right _ _)))).1
    (lt_of_lt_of_le hz (min_le_left _ _))

/-- The inverse placement explicitly. -/
theorem uφ_symm_apply (p : Point) : (uφBP n k m (us[m]'hm)).symm p =
    ((p.1 - sR n k m (us[m]'hm) - 3) * ((tmplDBP (us[m]'hm).kind : ℝ) * sR n k m (us[m]'hm)),
      (p.2 - ((unitInputBP n k m (us[m]'hm)).H : ℝ) + 1) *
        ((tmplDBP (us[m]'hm).kind : ℝ) * sR n k m (us[m]'hm))) := by
  apply (uφBP n k m (us[m]'hm)).injective
  rw [AffineEquiv.apply_symm_apply, uφ_apply hQ hm]
  have hD : (0 : ℝ) < tmplDBP (us[m]'hm).kind := by exact_mod_cast tmplDBP_pos _
  have hS : (0 : ℝ) < sR n k m (us[m]'hm) := by linarith [sR_ge hQ hm]
  ext <;> simp only <;> field_simp <;> ring

/-- The inverse placement scales determinants by `(D S)²`. -/
theorem det_uφ_symm (a b c : Point) :
    det ((uφBP n k m (us[m]'hm)).symm a) ((uφBP n k m (us[m]'hm)).symm b)
      ((uφBP n k m (us[m]'hm)).symm c) =
      ((tmplDBP (us[m]'hm).kind : ℝ) * sR n k m (us[m]'hm)) ^ 2 * det a b c := by
  rw [uφ_symm_apply hQ hm, uφ_symm_apply hQ hm, uφ_symm_apply hQ hm]
  simp only [det]; ring

theorem uφ_symm_cont : Continuous (uφBP n k m (us[m]'hm)).symm :=
  AffineEquiv.continuous_of_finiteDimensional _

theorem uφ_symm_lerp (a b : Point) (t : ℝ) : (uφBP n k m (us[m]'hm)).symm (Geometry.lerp a b t) =
    Geometry.lerp ((uφBP n k m (us[m]'hm)).symm a) ((uφBP n k m (us[m]'hm)).symm b) t := by
  rw [uφ_symm_apply hQ hm, uφ_symm_apply hQ hm, uφ_symm_apply hQ hm]
  ext <;> simp only [Geometry.lerp] <;> ring

/-- Transfer of a half-ball from template coordinates. -/
theorem halfball_transfer {y : Point} {T : Set Point} {f : Point → ℝ}
    (h : ∃ r > 0, ∀ x', dist x' ((uφBP n k m (us[m]'hm)).symm y) < r → 0 ≤ f x' → x' ∈ T) :
    ∃ r > 0, ∀ z, dist z y < r → 0 ≤ f ((uφBP n k m (us[m]'hm)).symm z) →
      z ∈ uφBP n k m (us[m]'hm) '' T := by
  obtain ⟨r, hr, h⟩ := h
  have hc := (uφ_symm_cont hQ hm).continuousAt (x := y)
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hc r hr
  exact ⟨δ, hδ, fun z hz hf => ⟨_, h _ (hball hz) hf, AffineEquiv.apply_symm_apply _ _⟩⟩

theorem c1_bdry : ratPoint (c1 (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H) ∈
    Q.boundary :=
  lowerWall_bdry hQ hm (Geometry.left_mem_segment _ _)

theorem d1_bdry : ratPoint (d1 (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H) ∈
    Q.boundary := by
  apply upperWall_bdry hQ hm; rw [Geometry.segment_comm]; exact Geometry.left_mem_segment _ _

theorem v0_bdry : uφBP n k m (us[m]'hm) (intPoint (cv (tmplVBP (us[m]'hm).kind) 0)) ∈ Q.boundary := by
  apply lowerWall_bdry hQ hm; rw [Geometry.segment_comm]; exact Geometry.left_mem_segment _ _

theorem vl_bdry : uφBP n k m (us[m]'hm) (intPoint (cv (tmplVBP (us[m]'hm).kind)
    ((tmplVBP (us[m]'hm).kind).length - 1))) ∈ Q.boundary :=
  upperWall_bdry hQ hm (Geometry.left_mem_segment _ _)

theorem uφ_c1T : uφBP n k m (us[m]'hm) ((chanOfBP (us[m]'hm).kind).c1.pt (sR n k m (us[m]'hm))) =
    ratPoint (c1 (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H) := by
  rw [← uφ_symm_c1 hQ hm, AffineEquiv.apply_symm_apply]

theorem uφ_d1T : uφBP n k m (us[m]'hm) ((chanOfBP (us[m]'hm).kind).d1.pt (sR n k m (us[m]'hm))) =
    ratPoint (d1 (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H) := by
  rw [← uφ_symm_d1 hQ hm, AffineEquiv.apply_symm_apply]

omit hQ hm in
/-- A point of a segment other than its ends, `lerp` form. -/
theorem open_of_not_ends {a b y : Point} (hy : y ∈ ArtGallery.segment a b) (ha : y ≠ a)
    (hb : y ≠ b) : ∃ t, 0 < t ∧ t < 1 ∧ y = Geometry.lerp a b t := by
  obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hy
  refine ⟨t, lt_of_le_of_ne ht0 ?_, lt_of_le_of_ne ht1 ?_, rfl⟩
  · rintro rfl; exact ha (Geometry.lerp_zero _ _)
  · rintro rfl; exact hb (Geometry.lerp_one _ _)

/-- **The window**: a point of the window off the boundary is an interior point of the corridor
together with the channel. -/
theorem window_interior {y : Point} (hy : y ∈ (unitInputBP n k m (us[m]'hm)).window)
    (hyb : y ∉ Q.boundary) : y ∈ interior (corG n k m (us[m]'hm) ∪ chanG n k m (us[m]'hm)) := by
  have hcb := cb_pos hQ hm
  have hca := ca_pos hQ hm
  have hg := hQ.good hm
  set I := unitInputBP n k m (us[m]'hm) with hI
  have hCo := chan_corners hQ hm
  obtain ⟨t, ht0, ht1, rfl⟩ := open_of_not_ends hy (fun h => hyb (h ▸ c1_bdry hQ hm))
    (fun h => hyb (h ▸ d1_bdry hQ hm))
  refine mem_interior_of_halves (fun z => det (ratPoint (c1 I.S I.H)) (ratPoint (d1 I.S I.H)) z)
    ?_ ?_
  · -- the corridor side
    have hn : I.poly.n = I.chainBefore.length + I.chainAfter.length := by
      rw [poly_n]; simp
    have e1 : I.poly.vtx (I.chainBefore.length - 1) = ratPoint (c1 I.S I.H) := by
      rw [poly_vtx_before (by omega), chainBefore_getD_last]
    have e2 : I.poly.vtx ((I.chainBefore.length - 1 + 1) % I.poly.n) = ratPoint (d1 I.S I.H) := by
      rw [show I.chainBefore.length - 1 + 1 = I.chainBefore.length by omega,
        Nat.mod_eq_of_lt (by omega), poly_vtx_after le_rfl (by omega), Nat.sub_self,
        chainAfter_getD_zero]
    obtain ⟨r, hr, h⟩ := Polygon.local_halfplane hg.poly_simple hg.poly_interiorLeft
      (i := I.chainBefore.length - 1) (by omega) ht0 ht1
    rw [e1, e2, ← Geometry.lerp_eq_add_smul] at h
    exact ⟨r, hr, fun z hz hf => Or.inl ((h z hz).2 hf)⟩
  · -- the channel side
    set c1T := (chanOfBP (us[m]'hm).kind).c1.pt (sR n k m (us[m]'hm))
    set d1T := (chanOfBP (us[m]'hm).kind).d1.pt (sR n k m (us[m]'hm))
    set v0T := (chanOfBP (us[m]'hm).kind).v0.pt (sR n k m (us[m]'hm))
    set vlT := (chanOfBP (us[m]'hm).kind).vl.pt (sR n k m (us[m]'hm))
    have hx : (uφBP n k m (us[m]'hm)).symm (Geometry.lerp (ratPoint (c1 I.S I.H))
        (ratPoint (d1 I.S I.H)) t) = Geometry.lerp c1T d1T t := by
      rw [uφ_symm_lerp hQ hm, uφ_symm_c1 hQ hm, uφ_symm_d1 hQ hm]
    have a0 : 0 < det c1T v0T (Geometry.lerp c1T d1T t) := by
      rw [Geometry.det_lerp, Geometry.det_self_outer, Geometry.det_cyclic d1T c1T v0T]
      have := hCo.t3; nlinarith
    have a1 : 0 < det v0T vlT (Geometry.lerp c1T d1T t) := by
      rw [Geometry.det_lerp, Geometry.det_cyclic c1T v0T vlT]
      have := hCo.t0; have := hCo.t1; nlinarith
    have a2 : 0 < det vlT d1T (Geometry.lerp c1T d1T t) := by
      rw [Geometry.det_lerp, Geometry.det_self_right]
      have := hCo.t2; nlinarith
    obtain ⟨r, hr, h⟩ := halfball_transfer hQ hm (y := Geometry.lerp (ratPoint (c1 I.S I.H))
      (ratPoint (d1 I.S I.H)) t) (T := chanT n k m (us[m]'hm)) (f := fun x' => det d1T c1T x')
      (by
        rw [hx]
        obtain ⟨r, hr, h⟩ := chan_halfball (c1 := c1T) (v0 := v0T) (vl := vlT) (d1 := d1T)
          (x := Geometry.lerp c1T d1T t) 3 (fun j hj => by
            fin_cases j
            · exact a0
            · exact a1
            · exact a2
            · exact absurd rfl hj)
        exact ⟨r, hr, fun x' hx' hf => h x' hx' hf⟩)
    refine ⟨r, hr, fun z hz hf => Or.inr (h z hz ?_)⟩
    have e1 : c1T = (uφBP n k m (us[m]'hm)).symm (ratPoint (c1 I.S I.H)) := (uφ_symm_c1 hQ hm).symm
    have e2 : d1T = (uφBP n k m (us[m]'hm)).symm (ratPoint (d1 I.S I.H)) := (uφ_symm_d1 hQ hm).symm
    show 0 ≤ det d1T c1T _
    rw [e1, e2, det_uφ_symm hQ hm, Geometry.det_swap12]
    have := sq_nonneg ((tmplDBP (us[m]'hm).kind : ℝ) * sR n k m (us[m]'hm))
    nlinarith

/-- **The mouth**: a point of the mouth off the boundary is an interior point of the channel
together with the template room. -/
theorem mouth_interior {y : Point} (hy : y ∈ uφBP n k m (us[m]'hm) '' tMouthBP (us[m]'hm).kind)
    (hyb : y ∉ Q.boundary) : y ∈ interior (chanG n k m (us[m]'hm) ∪ tkG n k m (us[m]'hm)) := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hCo := chan_corners hQ hm
  have hl := tmplBP_length (us[m]'hm).kind
  set c1T := (chanOfBP (us[m]'hm).kind).c1.pt (sR n k m (us[m]'hm))
  set d1T := (chanOfBP (us[m]'hm).kind).d1.pt (sR n k m (us[m]'hm))
  set v0T := (chanOfBP (us[m]'hm).kind).v0.pt (sR n k m (us[m]'hm)) with hv0T
  set vlT := (chanOfBP (us[m]'hm).kind).vl.pt (sR n k m (us[m]'hm)) with hvlT
  have ev0 : v0T = intPoint (cv (tmplVBP (us[m]'hm).kind) 0) := by rw [hv0T, ChanD.v0_pt, chanOfBP_V]
  have evl : vlT = intPoint (cv (tmplVBP (us[m]'hm).kind) ((tmplVBP (us[m]'hm).kind).length - 1)) := by
    rw [hvlT, ChanD.vl_pt, chanOfBP_V]
  rw [tMouthBP, ← ev0, ← evl] at hx
  obtain ⟨t, ht0, ht1, rfl⟩ := open_of_not_ends hx
    (fun h => hyb (by rw [h, evl]; exact vl_bdry hQ hm))
    (fun h => hyb (by rw [h, ev0]; exact v0_bdry hQ hm))
  have hint : Geometry.lerp vlT v0T t ∈ interior (chanT n k m (us[m]'hm) ∪ (tKBP (us[m]'hm).kind).filled) := by
    refine mem_interior_of_halves (fun z => det v0T vlT z) ?_ ?_
    · -- the channel side
      have a0 : 0 < det c1T v0T (Geometry.lerp vlT v0T t) := by
        rw [Geometry.det_lerp, Geometry.det_self_right]
        have := hCo.t0; nlinarith
      have a2 : 0 < det vlT d1T (Geometry.lerp vlT v0T t) := by
        rw [Geometry.det_lerp, Geometry.det_self_outer, Geometry.det_cyclic v0T vlT d1T]
        have := hCo.t1; nlinarith
      have a3 : 0 < det d1T c1T (Geometry.lerp vlT v0T t) := by
        rw [Geometry.det_lerp, Geometry.det_cyclic vlT d1T c1T]
        have := hCo.t2; have := hCo.t3; nlinarith
      obtain ⟨r, hr, h⟩ := chan_halfball (c1 := c1T) (v0 := v0T) (vl := vlT) (d1 := d1T)
        (x := Geometry.lerp vlT v0T t) 1 (fun j hj => by
          fin_cases j
          · exact a0
          · exact absurd rfl hj
          · exact a2
          · exact a3)
      exact ⟨r, hr, fun z hz hf => Or.inl (h z hz hf)⟩
    · -- the template room side
      have hn : (tKBP (us[m]'hm).kind).n = (tmplVBP (us[m]'hm).kind).length := n_map_intPoint _
      have e1 : (tKBP (us[m]'hm).kind).vtx ((tmplVBP (us[m]'hm).kind).length - 1) = vlT := by
        rw [tKBP, vtx_map_intPoint, evl]
      have e2 : (tKBP (us[m]'hm).kind).vtx (((tmplVBP (us[m]'hm).kind).length - 1 + 1) %
          (tKBP (us[m]'hm).kind).n) = v0T := by
        rw [hn, show (tmplVBP (us[m]'hm).kind).length - 1 + 1 = (tmplVBP (us[m]'hm).kind).length by
          omega, Nat.mod_self, tKBP, vtx_map_intPoint, ev0]
      obtain ⟨r, hr, h⟩ := Polygon.local_halfplane (tKBP_simple _) (tKBP_ccw _)
        (i := (tmplVBP (us[m]'hm).kind).length - 1) (by rw [hn]; omega) ht0 ht1
      rw [e1, e2, ← Geometry.lerp_eq_add_smul] at h
      refine ⟨r, hr, fun z hz hf => Or.inr ((h z hz).2 ?_)⟩
      rw [Geometry.det_swap12]; linarith
  have := Set.mem_image_of_mem (uφBP n k m (us[m]'hm)) hint
  rw [Vis.Cert.image_interior_affine, Set.image_union] at this
  exact this

/-- The corridor off its doors. -/
theorem cor_interior {y : Point} (hy : y ∈ corG n k m (us[m]'hm)) (hyb : y ∉ Q.boundary)
    (hyw : y ∉ (unitInputBP n k m (us[m]'hm)).window)
    (hye : y ∉ (unitInputBP n k m (us[m]'hm)).entrance) : y ∈ interior (corG n k m (us[m]'hm)) :=
  interior_of_room hQ.simple ((hQ.good hm).corridor_isRoom hQ.simple hQ.ccw
    (hQ.corridorAt hm)) hy (corG_subset hQ hm hy) hyb (fun h => h.elim hyw hye)

/-- The template room off the mouth. -/
theorem tk_interior {y : Point} (hy : y ∈ tkG n k m (us[m]'hm)) (hyb : y ∉ Q.boundary)
    (hym : y ∉ uφBP n k m (us[m]'hm) '' tMouthBP (us[m]'hm).kind) :
    y ∈ interior (tkG n k m (us[m]'hm)) := by
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨hP', hL', hC', hS'⟩ := tFrame hQ hm
  have hxb : x ∉ (tPoly Q n k m (us[m]'hm)).boundary := by
    intro h
    rw [tPoly, Hardening.Invariance.boundary_mapPoly] at h
    obtain ⟨z, hz, hzx⟩ := h
    apply hyb; rw [← hzx, AffineEquiv.apply_symm_apply]; exact hz
  have := interior_of_room hP' (tKBP_room hP' hL' hC') hx (tKBP_subset hP' hL' hC' hS' hx) hxb
    (fun h => hym ⟨x, h, rfl⟩)
  rw [tkG, ← Vis.Cert.image_interior_affine]
  exact Set.mem_image_of_mem _ this

/-- Points of the channel off the boundary: interior points, window points or mouth points. -/
theorem chan_cases {y : Point} (hy : y ∈ chanG n k m (us[m]'hm)) (hyb : y ∉ Q.boundary) :
    y ∈ interior (chanG n k m (us[m]'hm)) ∨ y ∈ (unitInputBP n k m (us[m]'hm)).window ∨
      y ∈ uφBP n k m (us[m]'hm) '' tMouthBP (us[m]'hm).kind := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hCo := chan_corners hQ hm
  have ev0 : (chanOfBP (us[m]'hm).kind).v0.pt (sR n k m (us[m]'hm)) =
      intPoint (cv (tmplVBP (us[m]'hm).kind) 0) := by rw [ChanD.v0_pt, chanOfBP_V]
  have evl : (chanOfBP (us[m]'hm).kind).vl.pt (sR n k m (us[m]'hm)) =
      intPoint (cv (tmplVBP (us[m]'hm).kind) ((tmplVBP (us[m]'hm).kind).length - 1)) := by
    rw [ChanD.vl_pt, chanOfBP_V]
  have img : ∀ a b : Point, x ∈ ArtGallery.segment a b →
      uφBP n k m (us[m]'hm) x ∈ ArtGallery.segment (uφBP n k m (us[m]'hm) a)
        (uφBP n k m (us[m]'hm) b) := fun a b h => by
    rw [← Hardening.Invariance.image_segment']; exact Set.mem_image_of_mem _ h
  obtain ⟨g0, g1, g2, g3⟩ := hx
  by_cases hs : 0 < det ((chanOfBP (us[m]'hm).kind).c1.pt (sR n k m (us[m]'hm)))
      ((chanOfBP (us[m]'hm).kind).v0.pt (sR n k m (us[m]'hm))) x ∧
      0 < det ((chanOfBP (us[m]'hm).kind).v0.pt (sR n k m (us[m]'hm)))
      ((chanOfBP (us[m]'hm).kind).vl.pt (sR n k m (us[m]'hm))) x ∧
      0 < det ((chanOfBP (us[m]'hm).kind).vl.pt (sR n k m (us[m]'hm)))
      ((chanOfBP (us[m]'hm).kind).d1.pt (sR n k m (us[m]'hm))) x ∧
      0 < det ((chanOfBP (us[m]'hm).kind).d1.pt (sR n k m (us[m]'hm)))
      ((chanOfBP (us[m]'hm).kind).c1.pt (sR n k m (us[m]'hm))) x
  · left
    rw [chanG, ← Vis.Cert.image_interior_affine]
    exact Set.mem_image_of_mem _ (mem_interior_chanSet hs)
  have hxC : x ∈ chanT n k m (us[m]'hm) := ⟨g0, g1, g2, g3⟩
  simp only [not_and_or, not_lt] at hs
  rcases hs with h | h | h | h
  · exfalso
    have := img _ _ (chan_side0 hCo hxC (le_antisymm h g0))
    rw [uφ_c1T hQ hm, ev0] at this
    exact hyb (lowerWall_bdry hQ hm this)
  · right; right
    refine ⟨x, ?_, rfl⟩
    have := chan_side1 hCo hxC (le_antisymm h g1)
    rw [tMouthBP, Geometry.segment_comm, ← ev0, ← evl]; exact this
  · exfalso
    have := img _ _ (chan_side2 hCo hxC (le_antisymm h g2))
    rw [uφ_d1T hQ hm, evl] at this
    exact hyb (upperWall_bdry hQ hm this)
  · right; left
    have := img _ _ (chan_side3 hCo hxC (le_antisymm h g3))
    rw [uφ_c1T hQ hm, uφ_d1T hQ hm, Geometry.segment_comm] at this
    exact this

/-- **The unit region is a room with the entrance as door**: its points off the boundary of `Q`
and off the entrance are interior points. -/
theorem unitU_interior {y : Point} (hy : y ∈ unitU n k m (us[m]'hm)) (hyb : y ∉ Q.boundary)
    (hye : y ∉ (unitInputBP n k m (us[m]'hm)).entrance) : y ∈ interior (unitU n k m (us[m]'hm)) := by
  have s1 : corG n k m (us[m]'hm) ∪ chanG n k m (us[m]'hm) ⊆ unitU n k m (us[m]'hm) :=
    subset_union_left
  have s2 : chanG n k m (us[m]'hm) ∪ tkG n k m (us[m]'hm) ⊆ unitU n k m (us[m]'hm) := by
    rintro z (h | h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hw : y ∈ (unitInputBP n k m (us[m]'hm)).window → y ∈ interior (unitU n k m (us[m]'hm)) :=
    fun h => interior_mono s1 (window_interior hQ hm h hyb)
  have hmo : y ∈ uφBP n k m (us[m]'hm) '' tMouthBP (us[m]'hm).kind →
      y ∈ interior (unitU n k m (us[m]'hm)) :=
    fun h => interior_mono s2 (mouth_interior hQ hm h hyb)
  rcases hy with (h | h) | h
  · by_cases h' : y ∈ (unitInputBP n k m (us[m]'hm)).window
    · exact hw h'
    · exact interior_mono (subset_union_left.trans subset_union_left)
        (cor_interior hQ hm h hyb h' hye)
  · rcases chan_cases hQ hm h hyb with h' | h' | h'
    · exact interior_mono (subset_union_right.trans subset_union_left) h'
    · exact hw h'
    · exact hmo h'
  · by_cases h' : y ∈ uφBP n k m (us[m]'hm) '' tMouthBP (us[m]'hm).kind
    · exact hmo h'
    · exact interior_mono subset_union_right (tk_interior hQ hm h hyb h')

/-- **The unit chain lies in the unit region.** -/
theorem unitChain_subset : chainSet ((unitChainBP n k m (us[m]'hm)).map ratPoint) ⊆
    unitU n k m (us[m]'hm) := by
  intro z hz
  have hg := hQ.good hm
  have hCo := chan_corners hQ hm
  have ev0 : (chanOfBP (us[m]'hm).kind).v0.pt (sR n k m (us[m]'hm)) =
      intPoint (cv (tmplVBP (us[m]'hm).kind) 0) := by rw [ChanD.v0_pt, chanOfBP_V]
  have evl : (chanOfBP (us[m]'hm).kind).vl.pt (sR n k m (us[m]'hm)) =
      intPoint (cv (tmplVBP (us[m]'hm).kind) ((tmplVBP (us[m]'hm).kind).length - 1)) := by
    rw [ChanD.vl_pt, chanOfBP_V]
  rcases unit_piecesBP hg (us[m]'hm).kind hz with h | h | h | h | h
  · exact Or.inl (Or.inl (Polygon.boundary_subset_filled _ (chainSet_before_subset h)))
  · left; right
    rw [tmplFstBP_eq] at h
    have h' : z ∈ ArtGallery.segment (uφBP n k m (us[m]'hm) ((chanOfBP (us[m]'hm).kind).c1.pt
        (sR n k m (us[m]'hm)))) (uφBP n k m (us[m]'hm) ((chanOfBP (us[m]'hm).kind).v0.pt
        (sR n k m (us[m]'hm)))) := by
      rw [uφ_c1T hQ hm, ev0]; exact h
    rw [← Hardening.Invariance.image_segment'] at h'
    obtain ⟨x, hx, rfl⟩ := h'
    exact ⟨x, hCo.segment_subset hCo.c1_mem hCo.v0_mem hx, rfl⟩
  · right
    obtain ⟨j, hj, x, hx, rfl⟩ := mem_tmplPlacedBP hQ hm h
    refine ⟨x, Polygon.boundary_subset_filled _ ⟨j, by rw [tKBP, n_map_intPoint]; omega, ?_⟩, rfl⟩
    rw [tKBP, edge_map_intPoint, Nat.mod_eq_of_lt hj]; exact hx
  · left; right
    rw [tmplLstBP_eq] at h
    have h' : z ∈ ArtGallery.segment (uφBP n k m (us[m]'hm) ((chanOfBP (us[m]'hm).kind).vl.pt
        (sR n k m (us[m]'hm)))) (uφBP n k m (us[m]'hm) ((chanOfBP (us[m]'hm).kind).d1.pt
        (sR n k m (us[m]'hm)))) := by
      rw [uφ_d1T hQ hm, evl]; exact h
    rw [← Hardening.Invariance.image_segment'] at h'
    obtain ⟨x, hx, rfl⟩ := h'
    exact ⟨x, hCo.segment_subset hCo.vl_mem hCo.d1_mem hx, rfl⟩
  · exact Or.inl (Or.inl (Polygon.boundary_subset_filled _ (chainSet_after_subset h)))

theorem unitStart_lt : unitStartBP n k us st m + (unitChainBP n k m (us[m]'hm)).length ≤ Q.n :=
  hQ.end_le hm

theorem c0_bdry : ratPoint (c0 (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H) ∈
    Q.boundary := by
  have hl := unitChain_len hQ hm
  have hcb := cb_pos hQ hm
  have hend := hQ.end_le hm
  have hv := hQ.vtx m hm 0 (by omega)
  rw [Nat.add_zero] at hv
  refine ⟨unitStartBP n k us st m, by omega, ?_⟩
  rw [Polygon.edge, hv]
  have e : (unitChainBP n k m (us[m]'hm)).getD 0 0 =
      c0 (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H := by
    simp only [unitChainBP, List.append_assoc]
    rw [List.getD_append _ _ _ _ (by omega), chainBefore_getD_zero]
  rw [e]; exact Geometry.left_mem_segment _ _

theorem d0_bdry : ratPoint (d0 (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H) ∈
    Q.boundary := by
  have hl := unitChain_len hQ hm
  have hca := ca_pos hQ hm
  have hend := hQ.end_le hm
  have hv := hQ.vtx m hm ((unitChainBP n k m (us[m]'hm)).length - 1) (by omega)
  refine ⟨unitStartBP n k us st m + ((unitChainBP n k m (us[m]'hm)).length - 1), by omega, ?_⟩
  rw [Polygon.edge, hv]
  have hlp : (placedTmplBP (unitInputBP n k m (us[m]'hm)) (us[m]'hm).kind).length =
      (tmplVBP (us[m]'hm).kind).length := by simp [placedTmplBP]
  have e : (unitChainBP n k m (us[m]'hm)).getD ((unitChainBP n k m (us[m]'hm)).length - 1) 0 =
      d0 (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H := by
    rw [hl]
    simp only [unitChainBP]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, hlp]; omega)]
    simp only [List.length_append, hlp]
    rw [show (unitInputBP n k m (us[m]'hm)).chainBefore.length + (tmplVBP (us[m]'hm).kind).length +
      (unitInputBP n k m (us[m]'hm)).chainAfter.length - 1 -
      ((unitInputBP n k m (us[m]'hm)).chainBefore.length + (tmplVBP (us[m]'hm).kind).length) =
      (unitInputBP n k m (us[m]'hm)).chainAfter.length - 1 by omega, chainAfter_getD_last]
  rw [e]; exact Geometry.left_mem_segment _ _

/-- **Near the open entrance, the half-plane `x ≥ S` lies in the corridor.** -/
theorem entrance_halfball {y : Point} (hy : y ∈ (unitInputBP n k m (us[m]'hm)).entrance)
    (hyb : y ∉ Q.boundary) : ∃ r > 0, ∀ z, dist z y < r →
      ((unitInputBP n k m (us[m]'hm)).S : ℝ) ≤ z.1 → z ∈ corG n k m (us[m]'hm) := by
  have hcb := cb_pos hQ hm
  have hca := ca_pos hQ hm
  have hg := hQ.good hm
  obtain ⟨t, ht0, ht1, rfl⟩ := open_of_not_ends hy (fun h => hyb (h ▸ d0_bdry hQ hm))
    (fun h => hyb (h ▸ c0_bdry hQ hm))
  have hn : (unitInputBP n k m (us[m]'hm)).poly.n = (unitInputBP n k m (us[m]'hm)).chainBefore.length +
      (unitInputBP n k m (us[m]'hm)).chainAfter.length := by
    rw [poly_n]; simp
  have e1 : (unitInputBP n k m (us[m]'hm)).poly.vtx ((unitInputBP n k m (us[m]'hm)).poly.n - 1) =
      ratPoint (d0 (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H) := by
    rw [hn, poly_vtx_after (by omega) (by omega),
      show (unitInputBP n k m (us[m]'hm)).chainBefore.length +
        (unitInputBP n k m (us[m]'hm)).chainAfter.length - 1 -
        (unitInputBP n k m (us[m]'hm)).chainBefore.length =
        (unitInputBP n k m (us[m]'hm)).chainAfter.length - 1 by omega, chainAfter_getD_last]
  have e2 : (unitInputBP n k m (us[m]'hm)).poly.vtx (((unitInputBP n k m (us[m]'hm)).poly.n - 1 + 1) %
      (unitInputBP n k m (us[m]'hm)).poly.n) =
      ratPoint (c0 (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H) := by
    rw [show (unitInputBP n k m (us[m]'hm)).poly.n - 1 + 1 = (unitInputBP n k m (us[m]'hm)).poly.n by
      omega, Nat.mod_self, poly_vtx_before (by omega), chainBefore_getD_zero]
  obtain ⟨r, hr, h⟩ := Polygon.local_halfplane hg.poly_simple hg.poly_interiorLeft
    (i := (unitInputBP n k m (us[m]'hm)).poly.n - 1) (by omega) ht0 ht1
  rw [e1, e2, ← Geometry.lerp_eq_add_smul] at h
  refine ⟨r, hr, fun z hz hf => (h z hz).2 ?_⟩
  rw [ratPoint_d0', ratPoint_c0']
  simp only [det]
  have := hg.rhoR_pos
  nlinarith

end Unit

end ArtGallery.BP.CoverU

end
