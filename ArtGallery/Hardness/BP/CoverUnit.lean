module

public import ArtGallery.Hardness.BP.CoverKind
public import ArtGallery.Hardness.BP.Count

/-!
# Boundary-point variant, coverage: the pieces of a unit

As `Sec5/CoverUnit.lean`, for the boundary-point units.  For unit `m` of a side
`SideAtBP Q n k us st` (`u = us[m]`, corridor input `I = unitInputBP n k m u`, placement
`φ = Count.uφBP n k m u`, template polygon `P' = φ⁻¹(Q)`), the unit region is covered by three
pieces (`unitU`):

* the corridor `corG = I.poly.filled` (the Section 5 corridor, unchanged);
* the channel `chanG = φ(chanT)`, the quadrilateral `c1 φ(V₀) φ(V_l) d1` (`chanT` in template
  coordinates, certificate `CoverK.chanOfBP`);
* the template room `tkG = φ(tKBP.filled)`.

This file proves: the template frame (`tFrame`), the boundary of `Q` right of the window
consists of the channel walls and the template chain (`bdry_right`), **the channel lies in the
region** (`chanT_subset`), receiver guards see the window (`recv_sees_window'`), the distinguished
receiver sees the channel (`star_sees_chan'`), and the **coverage of a unit** (`unit_cover`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.BP.CoverU

open ArtGallery Set Polygon Vis.Cert Sec5.Tmpl ArtGallery.Sec5 CoverK
open ArtGallery.Sec5.CoverT (ChanD RecvD chanSet Corners corners_of_B chanB_parts chainOut_sound
  chanSet_subset_hull interior_chanSet mem_interior_chanSet convex_chanSet isClosed_chanSet
  recv_sees_window star_sees_chan KindCons placeR)
open ArtGallery.BP.Count (uφBP unitS_geBP)
open ArtGallery.Sec5.Count (getD_map_ratPoint)
open ArtGallery.Sec5.Corridor (CorridorAt c0 c1 d0 d1)
open ArtGallery.Sec5.Corridor.Input
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

/-! ### The pieces -/

/-- The polygon in the template coordinates of unit `m`. -/
noncomputable def tPoly (Q : Polygon) (n k m : ℕ) (u : UnitSpec) : Polygon :=
  Hardening.Invariance.mapPoly (uφBP n k m u).symm Q

/-- The scale as a real number. -/
noncomputable def sR (n k m : ℕ) (u : UnitSpec) : ℝ := ((unitInputBP n k m u).S : ℝ)

/-- The channel in template coordinates. -/
noncomputable def chanT (n k m : ℕ) (u : UnitSpec) : Set Point :=
  (chanOfBP u.kind).chan (sR n k m u)

/-- The channel. -/
noncomputable def chanG (n k m : ℕ) (u : UnitSpec) : Set Point := uφBP n k m u '' chanT n k m u

/-- The template room. -/
noncomputable def tkG (n k m : ℕ) (u : UnitSpec) : Set Point := uφBP n k m u '' (tKBP u.kind).filled

/-- The corridor. -/
noncomputable def corG (n k m : ℕ) (u : UnitSpec) : Set Point := (unitInputBP n k m u).poly.filled

/-- The region of the unit. -/
noncomputable def unitU (n k m : ℕ) (u : UnitSpec) : Set Point :=
  corG n k m u ∪ chanG n k m u ∪ tkG n k m u

theorem getD_map_intPoint (V : List IPt) (j : ℕ) :
    (V.map intPoint).getD j (0, 0) = intPoint (cv V j) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : V[j]? <;> simp [cv, List.getD_eq_getElem?_getD, h]

section Unit

variable {Q : Polygon} {n k : ℕ} {us : List UnitSpec} {st : ℕ} (hQ : SideAtBP Q n k us st)
  {m : ℕ} (hm : m < us.length)
include hQ hm

/-- The template frame of unit `m`. -/
theorem tFrame :
    (tPoly Q n k m (us[m]'hm)).Simple ∧ (tPoly Q n k m (us[m]'hm)).InteriorLeft ∧
      ChainAt (tPoly Q n k m (us[m]'hm)) (tmplVBP (us[m]'hm).kind) (hQ.tStart hm) ∧
      SepAt (tPoly Q n k m (us[m]'hm)) (tmplVBP (us[m]'hm).kind) (hQ.tStart hm)
        (tmplRBP (us[m]'hm).kind) :=
  ⟨hQ.tmpl_simple hm, hQ.tmpl_ccw hm, hQ.chainAt hm, hQ.sepAt hm⟩

theorem sR_ge : (800000 : ℝ) ≤ sR n k m (us[m]'hm) := (hQ.good hm).S_ge_real

theorem sR_eq : sR n k m (us[m]'hm) = (S n k : ℝ) := hQ.cast_S hm

theorem uφ_apply (p : Point) : uφBP n k m (us[m]'hm) p =
    (sR n k m (us[m]'hm) + 3 + p.1 / ((tmplDBP (us[m]'hm).kind : ℝ) * sR n k m (us[m]'hm)),
      ((unitInputBP n k m (us[m]'hm)).H : ℝ) - 1 +
        p.2 / ((tmplDBP (us[m]'hm).kind : ℝ) * sR n k m (us[m]'hm))) :=
  tmplMapBP_apply _ _ p

/-- The window corners in template coordinates. -/
theorem uφ_symm_c1 : (uφBP n k m (us[m]'hm)).symm (ratPoint (c1 (unitInputBP n k m (us[m]'hm)).S
    (unitInputBP n k m (us[m]'hm)).H)) = (chanOfBP (us[m]'hm).kind).c1.pt (sR n k m (us[m]'hm)) := by
  rw [ChanD.c1_pt, ratPoint_c1', uφBP, tmplMapBP_symm_c1 _ (unitS_geBP _ _ _ _)]
  simp [sR]

theorem uφ_symm_d1 : (uφBP n k m (us[m]'hm)).symm (ratPoint (d1 (unitInputBP n k m (us[m]'hm)).S
    (unitInputBP n k m (us[m]'hm)).H)) = (chanOfBP (us[m]'hm).kind).d1.pt (sR n k m (us[m]'hm)) := by
  have h2 := (chanB_parts (chanOfBP_ok (us[m]'hm).kind)).1
  rw [ChanD.d1_pt h2, ratPoint_d1', rhoR_eq, uφBP, tmplMapBP_symm_d1 _ (unitS_geBP _ _ _ _)]
  simp [sR]

/-- The template chain edge `j`, placed. -/
theorem mem_tmplPlacedBP {z : Point} (hz : z ∈ chainSet (tmplPlacedBP (us[m]'hm).kind
    (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H
      (S_ne_of (hQ.good hm).S_ge_k))) :
    ∃ j, j + 1 < (tmplVBP (us[m]'hm).kind).length ∧ ∃ x ∈ ArtGallery.segment
      (intPoint (cv (tmplVBP (us[m]'hm).kind) j)) (intPoint (cv (tmplVBP (us[m]'hm).kind) (j + 1))),
        uφBP n k m (us[m]'hm) x = z := by
  rw [tmplPlacedBP_eq _ (hQ.good hm).S_ge_k, chainSet_map] at hz
  obtain ⟨x, hx, hxz⟩ := hz
  obtain ⟨j, hj, hxj⟩ := mem_chainSet_iff.1 hx
  simp only [List.length_map] at hj
  refine ⟨j, hj, x, ?_, hxz⟩
  simp only [edgeSeg] at hxj
  rwa [getD_map_intPoint, getD_map_intPoint] at hxj

/-- **The boundary right of the window**: a boundary point of `Q` right of `x = S + 2` at the
height of unit `m` lies on the lower channel wall, on a template chain edge, or on the upper
channel wall. -/
theorem bdry_right {z : Point} (hz : z ∈ Q.boundary) (hx : sR n k m (us[m]'hm) + 2 < z.1)
    (hy1 : (S n k : ℝ) + 3 * m - 0.4 ≤ z.2) (hy2 : z.2 ≤ (S n k : ℝ) + 3 * m + 2.6) :
    z ∈ ArtGallery.segment (ratPoint (c1 (unitInputBP n k m (us[m]'hm)).S
        (unitInputBP n k m (us[m]'hm)).H))
        (uφBP n k m (us[m]'hm) (intPoint (cv (tmplVBP (us[m]'hm).kind) 0))) ∨
      (∃ j, j + 1 < (tmplVBP (us[m]'hm).kind).length ∧ ∃ x ∈ ArtGallery.segment
        (intPoint (cv (tmplVBP (us[m]'hm).kind) j)) (intPoint (cv (tmplVBP (us[m]'hm).kind) (j + 1))),
          uφBP n k m (us[m]'hm) x = z) ∨
      z ∈ ArtGallery.segment (uφBP n k m (us[m]'hm) (intPoint (cv (tmplVBP (us[m]'hm).kind)
        ((tmplVBP (us[m]'hm).kind).length - 1))))
        (ratPoint (d1 (unitInputBP n k m (us[m]'hm)).S (unitInputBP n k m (us[m]'hm)).H)) := by
  have hg := hQ.good hm
  have eS := sR_eq hQ hm
  have hS2 : (S n k : ℝ) < z.1 := by rw [← eS]; linarith
  have hon := hQ.on_unit hm hz hS2 ⟨hy1, hy2⟩
  have hbox := hg.poly_filled_box (I := unitInputBP n k m (us[m]'hm))
  rcases unit_piecesBP hg (us[m]'hm).kind hon with h | h | h | h | h
  · exfalso
    have := (hbox (Polygon.boundary_subset_filled _ (chainSet_before_subset h))).2.1
    simp only [sR] at hx; linarith
  · left
    rwa [tmplFstBP_eq] at h
  · right; left
    exact mem_tmplPlacedBP hQ hm h
  · right; right
    rwa [tmplLstBP_eq] at h
  · exfalso
    have := (hbox (Polygon.boundary_subset_filled _ (chainSet_after_subset h))).2.1
    simp only [sR] at hx; linarith

/-! ### The channel lies in the region -/

omit hQ hm in
theorem cv_box (kd : Kind) (j : ℕ) :
    -(50 * (tmplDBP kd : ℝ)) ≤ (intPoint (cv (tmplVBP kd) j)).1 ∧
      (intPoint (cv (tmplVBP kd) j)).1 ≤ 50 * (tmplDBP kd : ℝ) ∧
      -(50 * (tmplDBP kd : ℝ)) ≤ (intPoint (cv (tmplVBP kd) j)).2 ∧
      (intPoint (cv (tmplVBP kd) j)).2 ≤ 50 * (tmplDBP kd : ℝ) := by
  by_cases hj : j < (tmplVBP kd).length
  · have h := boxOK_mem (tmplBP_boxOK kd) (cv (tmplVBP kd) j) (by
      simp only [cv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      exact List.getElem_mem _)
    obtain ⟨a, b, c, d⟩ := h
    simp only [intPoint_fst, intPoint_snd]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> exact_mod_cast ‹_›
  · have : cv (tmplVBP kd) j = (0, 0) := by
      simp [cv, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (tmplVBP kd).length ≤ j)]
    rw [this]
    have : (0 : ℝ) ≤ tmplDBP kd := by exact_mod_cast (tmplDBP_pos kd).le
    simp only [intPoint_fst, intPoint_snd, Int.cast_zero]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The corners of the channel turn left. -/
theorem chan_corners : Corners ((chanOfBP (us[m]'hm).kind).c1.pt (sR n k m (us[m]'hm)))
    ((chanOfBP (us[m]'hm).kind).v0.pt (sR n k m (us[m]'hm)))
    ((chanOfBP (us[m]'hm).kind).vl.pt (sR n k m (us[m]'hm)))
    ((chanOfBP (us[m]'hm).kind).d1.pt (sR n k m (us[m]'hm))) :=
  corners_of_B (chanB_parts (chanOfBP_ok _)).2.2.1 (sR_ge hQ hm)

/-- The box of the channel in template coordinates. -/
theorem chanT_box {x : Point} (hx : x ∈ chanT n k m (us[m]'hm)) :
    -((tmplDBP (us[m]'hm).kind : ℝ) * sR n k m (us[m]'hm)) ≤ x.1 ∧
      x.1 ≤ 50 * (tmplDBP (us[m]'hm).kind : ℝ) ∧ -(50 * (tmplDBP (us[m]'hm).kind : ℝ)) ≤ x.2 ∧
      x.2 ≤ (tmplDBP (us[m]'hm).kind : ℝ) * sR n k m (us[m]'hm) +
        3 / 2 * (tmplDBP (us[m]'hm).kind : ℝ) := by
  set D : ℝ := (tmplDBP (us[m]'hm).kind : ℝ)
  set Sr := sR n k m (us[m]'hm)
  have hS := sR_ge hQ hm
  have hD : 0 < D := by simp only [D]; exact_mod_cast tmplDBP_pos _
  have h2 := (chanB_parts (chanOfBP_ok (us[m]'hm).kind)).1
  have hbox : Convex ℝ {x : Point | -(D * Sr) ≤ x.1 ∧ x.1 ≤ 50 * D ∧ -(50 * D) ≤ x.2 ∧
      x.2 ≤ D * Sr + 3 / 2 * D} := by
    intro p hp q hq a b ha hb hab
    simp only [mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hp hq ⊢
    obtain ⟨p1, p2, p3, p4⟩ := hp
    obtain ⟨q1, q2, q3, q4⟩ := hq
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  have hsub := convexHull_min (t := {x : Point | -(D * Sr) ≤ x.1 ∧ x.1 ≤ 50 * D ∧
    -(50 * D) ≤ x.2 ∧ x.2 ≤ D * Sr + 3 / 2 * D}) ?_ hbox
    (chanSet_subset_hull (chan_corners hQ hm) hx)
  · exact hsub
  · intro p hp
    have hD' : (chanOfBP (us[m]'hm).kind).D = (tmplDBP (us[m]'hm).kind : ℤ) := chanOfBP_D _
    simp only [mem_insert_iff, mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · rw [ChanD.c1_pt, hD']
      simp only [mem_ofPred_eq, Int.cast_natCast]
      refine ⟨le_refl _, ?_, ?_, ?_⟩ <;> nlinarith
    · rw [ChanD.v0_pt, chanOfBP_V]
      obtain ⟨a, b, c, d⟩ := cv_box (us[m]'hm).kind 0
      exact ⟨by nlinarith, b, c, by nlinarith⟩
    · rw [ChanD.vl_pt, chanOfBP_V]
      obtain ⟨a, b, c, d⟩ := cv_box (us[m]'hm).kind ((tmplVBP (us[m]'hm).kind).length - 1)
      exact ⟨by nlinarith, b, c, by nlinarith⟩
    · rw [ChanD.d1_pt h2, hD']
      simp only [mem_ofPred_eq, Int.cast_natCast]
      refine ⟨le_refl _, ?_, ?_, le_refl _⟩ <;> nlinarith

omit hQ hm in
/-- A point of a segment `[a, b]` is on the line `a b`. -/
theorem det_eq_zero_of_mem {a b x : Point} (hx : x ∈ ArtGallery.segment a b) : det a b x = 0 := by
  obtain ⟨t, -, -, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
  exact Geometry.det_lerp_self a b t

/-- The global coordinates of a channel point. -/
theorem chan_glob {x : Point} (hx : x ∈ chanT n k m (us[m]'hm)) :
    sR n k m (us[m]'hm) + 2 ≤ (uφBP n k m (us[m]'hm) x).1 ∧
      (S n k : ℝ) + 3 * m - 0.4 ≤ (uφBP n k m (us[m]'hm) x).2 ∧
      (uφBP n k m (us[m]'hm) x).2 ≤ (S n k : ℝ) + 3 * m + 2.6 := by
  obtain ⟨b1, -, b3, b4⟩ := chanT_box hQ hm hx
  have hS := sR_ge hQ hm
  have hD : (1 : ℝ) ≤ (tmplDBP (us[m]'hm).kind : ℝ) := by exact_mod_cast tmplDBP_pos _
  have hDS : 0 < (tmplDBP (us[m]'hm).kind : ℝ) * sR n k m (us[m]'hm) := by positivity
  have eH := hQ.cast_H hm
  have eS := sR_eq hQ hm
  rw [uφ_apply hQ hm, eH]
  simp only
  refine ⟨?_, ?_, ?_⟩
  · have : -1 ≤ x.1 / ((tmplDBP (us[m]'hm).kind : ℝ) * sR n k m (us[m]'hm)) := by
      rw [le_div_iff₀ hDS]; linarith
    linarith
  · have : -(1 / 100) ≤ x.2 / ((tmplDBP (us[m]'hm).kind : ℝ) * sR n k m (us[m]'hm)) := by
      rw [le_div_iff₀ hDS]; nlinarith
    rw [← eS]; linarith
  · have : x.2 / ((tmplDBP (us[m]'hm).kind : ℝ) * sR n k m (us[m]'hm)) ≤ 1 + 1 / 2 := by
      rw [div_le_iff₀ hDS]; nlinarith
    rw [← eS]; linarith

/-- Strictly right of the window. -/
theorem chan_glob_strict {x : Point} (_hx : x ∈ chanT n k m (us[m]'hm))
    (h3 : 0 < det ((chanOfBP (us[m]'hm).kind).d1.pt (sR n k m (us[m]'hm)))
      ((chanOfBP (us[m]'hm).kind).c1.pt (sR n k m (us[m]'hm))) x) :
    sR n k m (us[m]'hm) + 2 < (uφBP n k m (us[m]'hm) x).1 := by
  have h2 := (chanB_parts (chanOfBP_ok (us[m]'hm).kind)).1
  have hD' : (chanOfBP (us[m]'hm).kind).D = (tmplDBP (us[m]'hm).kind : ℤ) := chanOfBP_D _
  rw [ChanD.d1_pt h2, ChanD.c1_pt, hD'] at h3
  simp only [det, Int.cast_natCast] at h3
  have hD : (1 : ℝ) ≤ (tmplDBP (us[m]'hm).kind : ℝ) := by exact_mod_cast tmplDBP_pos _
  have hS := sR_ge hQ hm
  have hDS : 0 < (tmplDBP (us[m]'hm).kind : ℝ) * sR n k m (us[m]'hm) := by positivity
  have hx1 : -((tmplDBP (us[m]'hm).kind : ℝ) * sR n k m (us[m]'hm)) < x.1 := by nlinarith
  rw [uφ_apply hQ hm]
  simp only
  have : -1 < x.1 / ((tmplDBP (us[m]'hm).kind : ℝ) * sR n k m (us[m]'hm)) := by
    rw [lt_div_iff₀ hDS]; linarith
  linarith

/-- No boundary point of `Q` is (the image of) an interior point of the channel. -/
theorem chan_interior_not_bdry {x : Point} (hx : x ∈ interior (chanT n k m (us[m]'hm)))
    (hxb : uφBP n k m (us[m]'hm) x ∈ Q.boundary) : False := by
  have hCo := chan_corners hQ hm
  obtain ⟨k0, k1, k2, k3⟩ := interior_chanSet hCo hx
  have hxC : x ∈ chanT n k m (us[m]'hm) := interior_subset hx
  obtain ⟨-, g2, g3⟩ := chan_glob hQ hm hxC
  have g1 := chan_glob_strict hQ hm hxC k3
  rcases bdry_right hQ hm hxb g1 g2 g3 with h | ⟨j, hj, y, hy, hyx⟩ | h
  · have h' : x ∈ ArtGallery.segment ((chanOfBP (us[m]'hm).kind).c1.pt (sR n k m (us[m]'hm)))
        ((chanOfBP (us[m]'hm).kind).v0.pt (sR n k m (us[m]'hm))) := by
      have := Set.mem_image_of_mem (uφBP n k m (us[m]'hm)).symm h
      rw [Hardening.Invariance.image_segment', AffineEquiv.symm_apply_apply,
        AffineEquiv.symm_apply_apply, uφ_symm_c1 hQ hm] at this
      rwa [ChanD.v0_pt, chanOfBP_V]
    rw [det_eq_zero_of_mem h'] at k0; exact lt_irrefl _ k0
  · have hyx' : y = x := (uφBP n k m (us[m]'hm)).injective hyx
    subst hyx'
    have hc := (chanB_parts (chanOfBP_ok (us[m]'hm).kind))
    refine chainOut_sound hc.2.2.1 hc.2.2.2.1 (sR_ge hQ hm) (by rwa [chanOfBP_V]) (z := y) ?_
      ⟨k0, k1, k2, k3⟩
    rwa [chanOfBP_V]
  · have h' : x ∈ ArtGallery.segment ((chanOfBP (us[m]'hm).kind).vl.pt (sR n k m (us[m]'hm)))
        ((chanOfBP (us[m]'hm).kind).d1.pt (sR n k m (us[m]'hm))) := by
      have := Set.mem_image_of_mem (uφBP n k m (us[m]'hm)).symm h
      rw [Hardening.Invariance.image_segment', AffineEquiv.symm_apply_apply,
        AffineEquiv.symm_apply_apply, uφ_symm_d1 hQ hm] at this
      rwa [ChanD.vl_pt, chanOfBP_V]
    rw [det_eq_zero_of_mem h'] at k2; exact lt_irrefl _ k2

omit hQ hm in
theorem lerp_half_eq_left {a b : Point} (h : Geometry.lerp a b (1 / 2) = a) : a = b := by
  ext
  · have := congrArg Prod.fst h; simp [Geometry.lerp] at this; linarith
  · have := congrArg Prod.snd h; simp [Geometry.lerp] at this; linarith

omit hQ hm in
theorem lerp_half_eq_right {a b : Point} (h : Geometry.lerp a b (1 / 2) = b) : a = b := by
  ext
  · have := congrArg Prod.fst h; simp [Geometry.lerp] at this; linarith
  · have := congrArg Prod.snd h; simp [Geometry.lerp] at this; linarith

/-- The midpoint of the mouth (template coordinates). -/
noncomputable def mouthMid (kd : Kind) : Point :=
  Geometry.lerp (intPoint (cv (tmplVBP kd) 0)) (intPoint (cv (tmplVBP kd) ((tmplVBP kd).length - 1)))
    (1 / 2)

omit hQ hm in
theorem mouthMid_mem_edge (kd : Kind) :
    mouthMid kd ∈ (tKBP kd).edge ((tmplVBP kd).length - 1) := by
  have hl := tmplBP_length kd
  rw [tKBP, edge_map_intPoint, show (tmplVBP kd).length - 1 + 1 = (tmplVBP kd).length by omega,
    Nat.mod_self, Geometry.segment_comm]
  exact Geometry.lerp_mem_segment _ _ (by norm_num) (by norm_num)

/-- **The midpoint of the mouth is not on the boundary of the template polygon.** -/
theorem mouthMid_not_bdry : mouthMid (us[m]'hm).kind ∉ (tPoly Q n k m (us[m]'hm)).boundary := by
  intro hb
  set kd := (us[m]'hm).kind with hkd
  have hCo := chan_corners hQ hm
  have hl := tmplBP_length kd
  rw [tPoly, Hardening.Invariance.boundary_mapPoly] at hb
  obtain ⟨z, hz, hzm⟩ := hb
  have hzm' : uφBP n k m (us[m]'hm) (mouthMid kd) = z := by
    rw [← hzm, AffineEquiv.apply_symm_apply]
  have ev0 : (chanOfBP kd).v0.pt (sR n k m (us[m]'hm)) = intPoint (cv (tmplVBP kd) 0) := by
    rw [ChanD.v0_pt, chanOfBP_V]
  have evl : (chanOfBP kd).vl.pt (sR n k m (us[m]'hm)) =
      intPoint (cv (tmplVBP kd) ((tmplVBP kd).length - 1)) := by
    rw [ChanD.vl_pt, chanOfBP_V]
  have hmC : mouthMid kd ∈ chanT n k m (us[m]'hm) := by
    refine hCo.segment_subset hCo.v0_mem hCo.vl_mem ?_
    rw [ev0, evl]; exact Geometry.lerp_mem_segment _ _ (by norm_num) (by norm_num)
  obtain ⟨-, g2, g3⟩ := chan_glob hQ hm hmC
  have k3 : 0 < det ((chanOfBP kd).d1.pt (sR n k m (us[m]'hm)))
      ((chanOfBP kd).c1.pt (sR n k m (us[m]'hm))) (mouthMid kd) := by
    rw [mouthMid, Geometry.det_lerp, ← ev0, ← evl]
    have a := hCo.t3
    have b := hCo.t2
    have := Geometry.det_cyclic ((chanOfBP kd).vl.pt (sR n k m (us[m]'hm)))
      ((chanOfBP kd).d1.pt (sR n k m (us[m]'hm))) ((chanOfBP kd).c1.pt (sR n k m (us[m]'hm)))
    nlinarith
  have g1 := chan_glob_strict hQ hm hmC k3
  rw [hzm'] at g1 g2 g3
  rcases bdry_right hQ hm hz g1 g2 g3 with h | ⟨j, hj, y, hy, hyx⟩ | h
  · have h' : mouthMid kd ∈ ArtGallery.segment ((chanOfBP kd).c1.pt (sR n k m (us[m]'hm)))
        ((chanOfBP kd).v0.pt (sR n k m (us[m]'hm))) := by
      have := Set.mem_image_of_mem (uφBP n k m (us[m]'hm)).symm h
      rw [Hardening.Invariance.image_segment', AffineEquiv.symm_apply_apply,
        uφ_symm_c1 hQ hm, ← hzm'] at this
      rw [ev0, AffineEquiv.symm_apply_apply] at *; assumption
    have h0 := det_eq_zero_of_mem h'
    rw [mouthMid, Geometry.det_lerp, ← ev0, ← evl, Geometry.det_self_right] at h0
    have := hCo.t0
    linarith
  · rw [← hkd] at hj hy
    have hyx' : y = mouthMid kd := (uφBP n k m (us[m]'hm)).injective (by rw [hyx, hzm'])
    rw [hyx'] at hy
    have hK := tKBP_simple kd
    have hn : (tKBP kd).n = (tmplVBP kd).length := n_map_intPoint _
    have hje : mouthMid kd ∈ (tKBP kd).edge j := by
      rw [tKBP, edge_map_intPoint, Nat.mod_eq_of_lt hj]; exact hy
    have hne : (tmplVBP kd).length - 1 ≠ j := by omega
    rcases Jordan.simple_endpoint_of_mem_two hK (by rw [hn]; omega) (by rw [hn]; omega) hne
      (mouthMid_mem_edge kd) hje with h | h
    · rw [tKBP, vtx_map_intPoint] at h
      exact hCo.ne12 (by rw [ev0, evl]; exact lerp_half_eq_right h)
    · rw [hn, show (tmplVBP kd).length - 1 + 1 = (tmplVBP kd).length by omega, Nat.mod_self, tKBP,
        vtx_map_intPoint] at h
      exact hCo.ne12 (by rw [ev0, evl]; exact lerp_half_eq_left h)
  · have h' : mouthMid kd ∈ ArtGallery.segment ((chanOfBP kd).vl.pt (sR n k m (us[m]'hm)))
        ((chanOfBP kd).d1.pt (sR n k m (us[m]'hm))) := by
      have := Set.mem_image_of_mem (uφBP n k m (us[m]'hm)).symm h
      rw [Hardening.Invariance.image_segment', AffineEquiv.symm_apply_apply,
        uφ_symm_d1 hQ hm, ← hzm'] at this
      rw [evl, AffineEquiv.symm_apply_apply] at *; assumption
    have h0 := det_eq_zero_of_mem h'
    rw [mouthMid, Geometry.det_lerp, ← ev0, ← evl, Geometry.det_self_outer] at h0
    have := hCo.t1
    have := Geometry.det_cyclic ((chanOfBP kd).v0.pt (sR n k m (us[m]'hm)))
      ((chanOfBP kd).vl.pt (sR n k m (us[m]'hm))) ((chanOfBP kd).d1.pt (sR n k m (us[m]'hm)))
    linarith

omit hQ hm in
theorem chanSet_subset_closure {c1 v0 vl d1 : Point} (h : Corners c1 v0 vl d1) :
    chanSet c1 v0 vl d1 ⊆ closure (interior (chanSet c1 v0 vl d1)) := by
  rw [convex_chanSet.closure_interior_eq_closure_of_nonempty_interior h.interior_nonempty,
    isClosed_chanSet.closure_eq]

theorem mouthMid_mem_chan : mouthMid (us[m]'hm).kind ∈ chanT n k m (us[m]'hm) := by
  have hCo := chan_corners hQ hm
  refine hCo.segment_subset hCo.v0_mem hCo.vl_mem ?_
  rw [ChanD.v0_pt, ChanD.vl_pt, chanOfBP_V]
  exact Geometry.lerp_mem_segment _ _ (by norm_num) (by norm_num)

/-- **The channel lies in the region** (template coordinates). -/
theorem chanT_subset : chanT n k m (us[m]'hm) ⊆ (tPoly Q n k m (us[m]'hm)).filled := by
  obtain ⟨hP', hL', hC', hS'⟩ := tFrame hQ hm
  have hCo := chan_corners hQ hm
  have hl := tmplBP_length (us[m]'hm).kind
  have hm0f : mouthMid (us[m]'hm).kind ∈ (tPoly Q n k m (us[m]'hm)).filled :=
    tKBP_subset hP' hL' hC' hS' (Polygon.boundary_subset_filled _
      ⟨(tmplVBP (us[m]'hm).kind).length - 1, by rw [tKBP, n_map_intPoint]; omega,
        mouthMid_mem_edge _⟩)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (Jordan.isOpen_filled_sdiff_boundary hP') _
    ⟨hm0f, mouthMid_not_bdry hQ hm⟩
  obtain ⟨p, hp, hpd⟩ := Metric.mem_closure_iff.1
    (chanSet_subset_closure hCo (mouthMid_mem_chan hQ hm)) r hr
  have hpf : p ∈ (tPoly Q n k m (us[m]'hm)).filled := (hball (by
    rw [Metric.mem_ball, dist_comm]; exact hpd)).1
  have hedge : ∀ i < (tPoly Q n k m (us[m]'hm)).n,
      Disjoint (interior (chanT n k m (us[m]'hm))) ((tPoly Q n k m (us[m]'hm)).edge i) := by
    intro i hi
    rw [Set.disjoint_left]
    intro x hx hxe
    have hxb : x ∈ (tPoly Q n k m (us[m]'hm)).boundary := ⟨i, hi, hxe⟩
    rw [tPoly, Hardening.Invariance.boundary_mapPoly] at hxb
    obtain ⟨z, hz, rfl⟩ := hxb
    exact chan_interior_not_bdry hQ hm hx (by rw [AffineEquiv.apply_symm_apply]; exact hz)
  exact subset_closure.trans
    (Polygon.closure_subset_filled_of_convex hP' convex_chanSet hedge hp hpf)

/-! ### Visibility in the unit, global coordinates -/

theorem sees_uφBP {a b : Point} : Q.Sees (uφBP n k m (us[m]'hm) a) (uφBP n k m (us[m]'hm) b) ↔
    (tPoly Q n k m (us[m]'hm)).Sees a b := by
  have := Vis.Cert.sees_mapPoly_iff (uφBP n k m (us[m]'hm)).symm Q (uφBP n k m (us[m]'hm) a)
    (uφBP n k m (us[m]'hm) b)
  rw [AffineEquiv.symm_apply_apply, AffineEquiv.symm_apply_apply] at this
  exact this.symm

theorem frame_chan :
    ChainAt (tPoly Q n k m (us[m]'hm)) (chanOfBP (us[m]'hm).kind).V (hQ.tStart hm) ∧
      SepAt (tPoly Q n k m (us[m]'hm)) (chanOfBP (us[m]'hm).kind).V (hQ.tStart hm)
        (tmplRBP (us[m]'hm).kind) := by
  obtain ⟨-, -, hC', hS'⟩ := tFrame hQ hm
  rw [chanOfBP_V]; exact ⟨hC', hS'⟩

/-- **A receiver guard sees the whole window** (global coordinates). -/
theorem recv_sees_window' {v : ℕ → ℝ} (hv : ∀ τ, 1 / 2 ≤ v τ ∧ v τ ≤ 2) {τ : ℕ}
    (hτ : τ < (tmplTBP (us[m]'hm).kind).length) :
    ∀ w ∈ (unitInputBP n k m (us[m]'hm)).window,
      Q.Sees (uφBP n k m (us[m]'hm) (tGuardBP (us[m]'hm).kind v (recvIdxBP (us[m]'hm).kind τ))) w := by
  intro w hw
  obtain ⟨hP', hL', hC', hS'⟩ := tFrame hQ hm
  obtain ⟨hC'', hS''⟩ := frame_chan hQ hm
  rw [← AffineEquiv.apply_symm_apply (uφBP n k m (us[m]'hm)) w, sees_uφBP hQ hm]
  have hr : (chanOfBP (us[m]'hm).kind).recv.getD τ default ∈ (chanOfBP (us[m]'hm).kind).recv := by
    have : τ < (chanOfBP (us[m]'hm).kind).recv.length := by rw [recvBP_length]; exact hτ
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; exact List.getElem_mem _
  refine recv_sees_window hP' hC'' hS'' (tRBP_subset hP' hL' hC' hS') (chanOfBP_ok _) (sR_ge hQ hm)
    (chanT_subset hQ hm) hr (tGuardBP_recv_mem _ hv hτ) ?_
  have := Set.mem_image_of_mem (uφBP n k m (us[m]'hm)).symm hw
  rwa [Corridor.Input.window, Hardening.Invariance.image_segment', uφ_symm_c1 hQ hm,
    uφ_symm_d1 hQ hm] at this

theorem star_lt : (chanOfBP (us[m]'hm).kind).star < (tmplTBP (us[m]'hm).kind).length := by
  rw [← recvBP_length]
  generalize (us[m]'hm).kind = kd
  cases kd <;> decide

/-- **The distinguished receiver guard sees the whole channel** (global coordinates). -/
theorem star_sees_chan' {v : ℕ → ℝ} (hv : ∀ τ, 1 / 2 ≤ v τ ∧ v τ ≤ 2) :
    ∀ z ∈ chanG n k m (us[m]'hm), Q.Sees (uφBP n k m (us[m]'hm)
      (tGuardBP (us[m]'hm).kind v (recvIdxBP (us[m]'hm).kind (chanOfBP (us[m]'hm).kind).star))) z := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hP', hL', hC', hS'⟩ := tFrame hQ hm
  obtain ⟨hC'', hS''⟩ := frame_chan hQ hm
  rw [sees_uφBP hQ hm]
  exact star_sees_chan hP' hC'' hS'' (tRBP_subset hP' hL' hC' hS') (chanOfBP_ok _) (sR_ge hQ hm)
    (chanT_subset hQ hm) (tGuardBP_recv_mem _ hv (star_lt hQ hm)) x hx

/-- **The template room is covered** (global coordinates). -/
theorem tk_cover {v : ℕ → ℝ} (hv : ∀ τ, 1 / 2 ≤ v τ ∧ v τ ≤ 2)
    (hc : KindCons (us[m]'hm).kind v) :
    ∀ z ∈ tkG n k m (us[m]'hm), ∃ j < tNumBP (us[m]'hm).kind, Q.Sees (uφBP n k m (us[m]'hm)
      (tGuardBP (us[m]'hm).kind v j)) z := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hP', hL', hC', hS'⟩ := tFrame hQ hm
  obtain ⟨j, hj, hX⟩ := tKBP_cover hP' hL' hC' hS' hv hc x hx
  exact ⟨j, hj, (sees_uφBP hQ hm).2 hX⟩

/-- The channel lies in the region (global coordinates). -/
theorem chanG_subset : chanG n k m (us[m]'hm) ⊆ Q.filled := by
  rintro _ ⟨x, hx, rfl⟩
  have := chanT_subset hQ hm hx
  rw [tPoly, Hardening.Invariance.filled_mapPoly] at this
  obtain ⟨y, hy, hyx⟩ := this
  rw [← hyx, AffineEquiv.apply_symm_apply]; exact hy

/-- The template room lies in the region (global coordinates). -/
theorem tkG_subset : tkG n k m (us[m]'hm) ⊆ Q.filled := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hP', hL', hC', hS'⟩ := tFrame hQ hm
  have := tKBP_subset hP' hL' hC' hS' hx
  rw [tPoly, Hardening.Invariance.filled_mapPoly] at this
  obtain ⟨y, hy, hyx⟩ := this
  rw [← hyx, AffineEquiv.apply_symm_apply]; exact hy

/-- The corridor lies in the region. -/
theorem corG_subset : corG n k m (us[m]'hm) ⊆ Q.filled :=
  (hQ.good hm).poly_subset hQ.simple hQ.ccw (hQ.corridorAt hm) (hQ.corridorClear hm)

/-! ### Coverage of the unit -/

theorem np_eq : (unitInputBP n k m (us[m]'hm)).np = (tmplTBP (us[m]'hm).kind).length :=
  (hQ.ok _ (List.getElem_mem hm)).len.trans (length_tmplTBP_eq _).symm

theorem umbraR_q_eq {v : ℕ → ℝ} {j : ℕ} (hj : j < (unitInputBP n k m (us[m]'hm)).np) :
    ((unitInputBP n k m (us[m]'hm)).umbraR j).q (v ((unitInputBP n k m (us[m]'hm)).tau j) - 1 / 2) =
      uφBP n k m (us[m]'hm) (tGuardBP (us[m]'hm).kind v
        (recvIdxBP (us[m]'hm).kind ((unitInputBP n k m (us[m]'hm)).tau j))) := by
  have hτ : (unitInputBP n k m (us[m]'hm)).tau j < (tmplTBP (us[m]'hm).kind).length := by
    rw [← np_eq hQ hm]; simp only [Corridor.Input.tau]; omega
  rw [uφBP, tGuardBP_recv_place _ v _ hτ, umbraR_q]
  simp only [Corridor.place, placeR, Corridor.Input.Tt]
  rfl

/-- **Coverage of a unit.**  Let `v τ ∈ [1/2, 2]` be receiver values satisfying the constraint of
the template, and assume that the base guard of every pair (offset `v(τ_j) − 1/2`) sees the
entrance.  Then every point of the unit region is seen by a base guard of the unit, a corridor
stationary guard, or a canonical template guard. -/
theorem unit_cover {v : ℕ → ℝ} (hv : ∀ τ, 1 / 2 ≤ v τ ∧ v τ ≤ 2)
    (hc : KindCons (us[m]'hm).kind v)
    (hent : ∀ j < (unitInputBP n k m (us[m]'hm)).np, ∀ w ∈ (unitInputBP n k m (us[m]'hm)).entrance,
      Q.Sees (((unitInputBP n k m (us[m]'hm)).umbraR j).p
        (v ((unitInputBP n k m (us[m]'hm)).tau j) - 1 / 2)) w) :
    ∀ z ∈ unitU n k m (us[m]'hm),
      (∃ j < (unitInputBP n k m (us[m]'hm)).np, Q.Sees (((unitInputBP n k m (us[m]'hm)).umbraR j).p
        (v ((unitInputBP n k m (us[m]'hm)).tau j) - 1 / 2)) z) ∨
      (∃ j < (unitInputBP n k m (us[m]'hm)).np,
        Q.Sees (ratPoint ((unitInputBP n k m (us[m]'hm)).sgPt j)) z) ∨
      (∃ j < tNumBP (us[m]'hm).kind,
        Q.Sees (uφBP n k m (us[m]'hm) (tGuardBP (us[m]'hm).kind v j)) z) := by
  rintro z ((hz | hz) | hz)
  · -- the corridor
    have hwin : ∀ j < (unitInputBP n k m (us[m]'hm)).np, ∀ w ∈ (unitInputBP n k m (us[m]'hm)).window,
        Q.Sees (((unitInputBP n k m (us[m]'hm)).umbraR j).q
          (v ((unitInputBP n k m (us[m]'hm)).tau j) - 1 / 2)) w := by
      intro j hj w hw
      rw [umbraR_q_eq hQ hm hj]
      have hτ : (unitInputBP n k m (us[m]'hm)).tau j < (tmplTBP (us[m]'hm).kind).length := by
        rw [← np_eq hQ hm]; simp only [Corridor.Input.tau]; omega
      exact recv_sees_window' hQ hm hv hτ w hw
    obtain ⟨j, hj, h⟩ := (hQ.good hm).corridor_covered_in hQ.simple hQ.ccw (hQ.corridorAt hm)
      (hQ.corridorClear hm) (t := fun j => v ((unitInputBP n k m (us[m]'hm)).tau j) - 1 / 2)
      (fun j _ => ⟨by linarith [(hv ((unitInputBP n k m (us[m]'hm)).tau j)).1],
        by linarith [(hv ((unitInputBP n k m (us[m]'hm)).tau j)).2]⟩) hent hwin hz
    rcases h with h | h | h
    · exact Or.inl ⟨j, hj, h⟩
    · rw [umbraR_q_eq hQ hm hj] at h
      exact Or.inr (Or.inr ⟨_, recvIdxBP_lt _ _, h⟩)
    · exact Or.inr (Or.inl ⟨j, hj, h⟩)
  · -- the channel
    exact Or.inr (Or.inr ⟨_, recvIdxBP_lt _ _, star_sees_chan' hQ hm hv z hz⟩)
  · -- the template room
    exact Or.inr (Or.inr (tk_cover hQ hm hv hc z hz))

end Unit

end ArtGallery.BP.CoverU

end
