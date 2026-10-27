module

public import ArtGallery.Stade.AdditionCover
public import ArtGallery.Stade.AdditionGeomGe

/-!
# Stade construction, §7: positive visibility in the addition gadget `addGe`

As `ArtGallery/Stade/AdditionCover.lean` for `addGe` (proof plan L7.7, L7.8), with the aux guard
at the canonical point `I = agI G v_x v_y` and the inputs at their values:

* `ag_aux_sees_bay`, `ag_input_sees_bay`: the aux guard and the z-input each see the whole bay
  `N1, N2, Q` (sight lines through the room's left side between `Q` and `N1`);
* `ag_pocketX_cover`, `ag_pocketY_cover`, `ag_pocketZ_cover` (chords argument): every point of
  each pocket is seen by the aux guard or by the input of the pocket (for the z-pocket, reached
  through the bay: if `v_z ≤ v_x + v_y`);
* `ag_aux_sees_room`, `ag_aux_sees_auxTri`: the aux guard sees the room and the aux wedge;
* `ag_needleZ_seen`, `ag_needleY_seen`: the inputs standing above the window see their needles
  hanging from the bottom of the room.
-/

@[expose] public section

namespace ArtGallery

namespace Stade

open ArtGallery.Geometry

variable {P : Polygon} {G : ℝ} {A : Set Point}

/-- The window of `addGe` lies in the hall `A` (if `A` contains it) and in the room. -/
theorem ag_window_mem (hWA : segment (agWL G) (agWR G) ⊆ A) :
    ∀ q : Point, q.2 = -1 → G + 85 ≤ q.1 → q.1 ≤ G + 363 → q ∈ A ∧ q ∈ piece (agRoom G) := by
  intro q h1 h2 h3
  have hq : q ∈ segment (agWL G) (agWR G) :=
    (mem_segment_horiz_iff (c := -1) (x₁ := G + 85) (x₂ := G + 363) (by linarith)).2 ⟨h1, h2, h3⟩
  exact ⟨hWA hq, agRoom_window hq⟩

/-- `addGe`: `0 < det N1 N2 I` (the canonical aux point sees `N2` through `[Q, N1]`). -/
theorem agI_N1N2 {vx vy : ℝ} (_hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy)
    (hy2 : vy ≤ 2) : 0 < det (agI G vx vy) (agN1 G) (agN2 G) := by
  have h := agI_lin_pos (G := G) (vx := vx) (vy := vy) hx2 (by linarith) (α := 538 / 25)
    (β := -35 / 2) (γ := -5355 / 8) (by unfold agS agSx agSy; linarith)
  have e : det (agI G vx vy) (agN1 G) (agN2 G) =
      538 / 25 * ((agI G vx vy).1 - G - 50) + -35 / 2 * (agI G vx vy).2 + -5355 / 8 := by
    simp only [det, agN1, agN2]; ring
  rw [e]; exact h

/-- **`addGe`: the aux guard sees the bay** (with the aux guard at `I(v_x, v_y)`). -/
theorem ag_aux_sees_bay (hRP : piece (agRoom G) ⊆ P.filled) (hBP : piece (agBay G) ⊆ P.filled)
    {vx vy : ℝ} (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy) (hy2 : vy ≤ 2) :
    ∀ x ∈ piece (agBay G), P.Sees (agI G vx vy) x := by
  intro x hx
  have hI := agI_mem_auxRegion (G := G) hx1 hx2 hy1 hy2
  have hIf := agI_fst (G := G) hx2 (by linarith : (0 : ℝ) ≤ vy)
  have hQN2 := (agI_pos (G := G) hx1 hx2 hy1 hy2).2.2.2.2.2.2
  refine add_sees_tri_through agBay_ccw (convex_piece _) hRP hBP hI.2 ?_ ?_ ?_
    (agI_N1N2 hx1 hx2 hy1 hy2).le hx
  · intro q hq
    obtain ⟨h1, h2, h3⟩ :=
      (mem_segment_vert_iff (c := G + 50) (y₁ := -151 / 3) (y₂ := -153 / 4) (by norm_num)).1 hq
    exact agRoom_left h1 (by linarith) (by linarith)
  · simp only [det, agQ, agN1]; nlinarith
  · have e : det (agI G vx vy) (agQ G) (agN2 G) =
        2831 / 300 * ((agI G vx vy).1 - G - 50) - 35 / 2 * (agI G vx vy).2 - 5285 / 6 := by
      simp only [det, agQ, agN2]; ring
    rw [e]; linarith

/-- **`addGe`: the z-input sees the bay** (through the window and the room's left side between
`Q` and `N1`). -/
theorem ag_input_sees_bay (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (agWL G) (agWR G) ⊆ A) (hRP : piece (agRoom G) ⊆ P.filled)
    (hBP : piece (agBay G) ⊆ P.filled) {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hgA : inPt (G + 185 / 2) v ∈ A) : ∀ x ∈ piece (agBay G), P.Sees (inPt (G + 185 / 2) v) x := by
  intro x hx
  have hB := agBay_ccw (G := G)
  obtain ⟨t0, t1, t2⟩ := mem_piece_tri.1 hx
  simp only [det, agN1, agN2, agQ] at t0 t1 t2
  have hx1 : x.1 ≤ G + 50 := by linarith
  have hx2 : x.2 < -1 := by linarith
  have hw1 : 0 ≤ det (inPt (G + 185 / 2) v) (G + 85, -1) x := by
    refine add_det_nonneg_tri hB hx ?_ ?_ ?_ <;>
      simp only [det, agN1, agN2, agQ, inPt_fst, inPt_snd] <;> linarith
  have hw2 : det (inPt (G + 185 / 2) v) (G + 363, -1) x ≤ 0 := by
    have sw : ∀ y, det ((G + 363, -1) : Point) (inPt (G + 185 / 2) v) y =
        -det (inPt (G + 185 / 2) v) (G + 363, -1) y := fun y => det_swap12 _ _ y
    have := add_det_nonneg_tri (A := ((G + 363, -1) : Point)) (B := inPt (G + 185 / 2) v) hB hx
      (by rw [sw]; simp only [det, agN1, inPt_fst, inPt_snd]; linarith)
      (by rw [sw]; simp only [det, agN2, inPt_fst, inPt_snd]; linarith)
      (by rw [sw]; simp only [det, agQ, inPt_fst, inPt_snd]; linarith)
    rw [sw] at this; linarith
  obtain ⟨q, hq, e1, e2, e3⟩ := add_cross_window (by linarith)
    (by simp only [inPt_snd]; linarith) hx2 hw1 hw2
  obtain ⟨hqA, hqR⟩ := ag_window_mem hWA q e1 e2 e3
  have hq1 : q.1 ≤ G + 185 / 2 := by
    obtain ⟨l, hl0, hl1, rfl⟩ := mem_segment_iff_lerp.1 hq
    simp only [lerp_fst, inPt_fst]
    nlinarith
  refine sees_of_mem_segment hq (sees_of_convex hA hAP hgA hqA) ?_
  refine add_sees_tri_through hB (convex_piece _) hRP hBP hqR ?_ ?_ ?_ ?_ hx
  · intro y hy
    obtain ⟨h1, h2, h3⟩ :=
      (mem_segment_vert_iff (c := G + 50) (y₁ := -151 / 3) (y₂ := -153 / 4) (by norm_num)).1 hy
    exact agRoom_left h1 (by linarith) (by linarith)
  · simp only [det, agQ, agN1]; rw [e1]; nlinarith
  · simp only [det, agQ, agN2]; rw [e1]; nlinarith
  · simp only [det, agN1, agN2]; rw [e1]; nlinarith

/-- **`addGe`, x-pocket (chords argument).**  With the aux guard at `I(v_x, v_y)` and the
x-input at `v_x`, every point of the x-pocket is seen by one of them. -/
theorem ag_pocketX_cover (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (agWL G) (agWR G) ⊆ A) (hRP : piece (agRoom G) ⊆ P.filled)
    (hXP : piece (agPocketX G) ⊆ P.filled) {vx vy : ℝ} (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2)
    (hy1 : 1 / 2 ≤ vy) (hy2 : vy ≤ 2) (hxA : inPt (G + 370) vx ∈ A) :
    ∀ p ∈ piece (agPocketX G), P.Sees (agI G vx vy) p ∨ P.Sees (inPt (G + 370) vx) p := by
  intro p hp
  obtain ⟨c1, c2, c3, c4⟩ := agPocketX_ccw (G := G)
  have hy0 : (0 : ℝ) ≤ vy := by linarith
  have hIf := agI_fst (G := G) hx2 hy0
  have hI := agI_mem_auxRegion (G := G) hx1 hx2 hy1 hy2
  obtain ⟨q0, q1, q2, q3⟩ := mem_piece_quad.1 hp
  simp only [det, agXlo, agN1, agP, agXhi] at q0 q1 q2 q3
  have hpd : p.1 ≤ G + 50 := by nlinarith
  have hpl : p.1 = G + 50 → -153 / 4 ≤ p.2 ∧ p.2 ≤ -37 := fun h => by
    rw [h] at q0 q2; constructor <;> linarith
  have hp2 : p.2 < -1 := by nlinarith
  have hmR : ∀ q : Point, q.1 = G + 50 → -153 / 4 ≤ q.2 → q.2 ≤ -37 → q ∈ piece (agRoom G) :=
    fun q h1 h2 h3 => agRoom_left h1 (by linarith) h3
  have hmC : segment ((G + 50, -153 / 4) : Point) (G + 50, -37) ⊆ piece (agPocketX G) :=
    add_mouth_subset c1 c2 c3 c4
  have hS := ag_shadows_mem hx1 hx2
  have hN1 := agI_N1 (G := G) hx1 hx2 hy1 hy2
  have hPin := ag_input_x_P (G := G) (v := vx) hx2
  have hIP := agI_P (G := G) hx2 hy0
  have hgN : (agN1 G).1 < (inPt (G + 370) vx).1 := by simp only [agN1, inPt_fst]; linarith
  have hlh : (agXlo G).2 < (agXhi G).2 := by simp only [agXlo, agXhi]; norm_num
  have hc : G + 30 < (agN1 G).1 := by simp only [agN1]; linarith
  have hs1 : (agXlo G).2 ≤ vproj (inPt (G + 370) vx) (agN1 G) (G + 30) := by
    rw [ag_shadow_x]; exact hS.1.1.le
  have ha_lo : 0 ≤ det (inPt (G + 370) vx) (agP G) (agXlo G) :=
    add_det_vert_nonneg (c := G + 30) (h := -2649 / 64) hgN (by linarith)
  have ha_dn : 0 ≤ det (inPt (G + 370) vx) (agP G) (agN1 G) := by
    simp only [det, agP, agN1, inPt_fst, inPt_snd]; nlinarith
  have ha_hi : 0 ≤ det (inPt (G + 370) vx) (agP G) (agXhi G) :=
    add_det_vert_nonneg (c := G + 30) (h := -2601 / 64) hgN (by linarith)
  have hb_lo : det (agI G vx vy) (agN1 G) (agXlo G) ≤ 0 :=
    add_det_vert_nonpos (c := G + 30) (h := -2649 / 64) hIf (by linarith)
  have hb_up : det (agI G vx vy) (agN1 G) (agP G) ≤ 0 := by
    simp only [det, agN1, agP]; nlinarith
  have hb_hi : det (agI G vx vy) (agN1 G) (agXhi G) ≤ 0 :=
    add_det_vert_nonpos (c := G + 30) (h := -2601 / 64) hIf (by linarith)
  have hb_lo' : 0 ≤ det (agI G vx vy) (agP G) (agXlo G) :=
    add_det_vert_nonneg (c := G + 30) (h := -2649 / 64) hIf (by rw [hIP]; exact hS.1.1.le)
  have hb_dn' : 0 ≤ det (agI G vx vy) (agP G) (agN1 G) := by
    simp only [det, agP, agN1]; nlinarith
  have hb_s : 0 ≤ det (agI G vx vy) (agP G)
      (G + 30, vproj (inPt (G + 370) vx) (agN1 G) (G + 30)) :=
    add_det_vert_nonneg hIf (by rw [hIP, ag_shadow_x])
  rcases add_pocket_split (lo := agXlo G) (dn := agN1 G) (up := agP G) (hi := agXhi G)
      (ga := inPt (G + 370) vx) (gb := agI G vx vy) (c := G + 30) c1 c3 c4 rfl rfl hlh hc hgN hs1
      ha_lo ha_dn ha_hi hb_lo hb_up hb_hi hb_lo' hb_dn' hb_s hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inr (add_sees_window_vmouth hA hAP (convex_piece _) hRP (convex_piece _) hXP
      (by linarith) (ag_window_mem hWA) (by norm_num) (by norm_num) hmR hmC hxA
      (by simp only [inPt_snd]; linarith) hgN hp hpd hpl hp2 ?_ ?_ h1 h2)
    · refine add_det_nonneg_quad c1 c3 hp ?_ ?_ ?_ ?_ <;>
        simp only [det, agXlo, agN1, agP, agXhi, inPt_fst, inPt_snd] <;> linarith
    · have sw : ∀ x, det ((G + 363, -1) : Point) (inPt (G + 370) vx) x =
          -det (inPt (G + 370) vx) (G + 363, -1) x := fun x => det_swap12 _ _ x
      have := add_det_nonneg_quad (A := ((G + 363, -1) : Point)) (B := inPt (G + 370) vx) c1 c3 hp
        (by simp only [det, agXlo, inPt_fst, inPt_snd]; linarith)
        (by simp only [det, agN1, inPt_fst, inPt_snd]; linarith)
        (by simp only [det, agP, inPt_fst, inPt_snd]; linarith)
        (by simp only [det, agXhi, inPt_fst, inPt_snd]; linarith)
      rw [sw] at this; linarith
  · exact Or.inl (add_sees_vmouth (convex_piece _) hRP (convex_piece _) hXP (by norm_num) hmR hmC
      hI.2 hIf hp hpd hpl h1 h2)

/-- **`addGe`, y-pocket (chords argument).**  With the aux guard at `I(v_x, v_y)` and the
y-input at `v_y`, every point of the y-pocket is seen by one of them. -/
theorem ag_pocketY_cover (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (agWL G) (agWR G) ⊆ A) (hRP : piece (agRoom G) ⊆ P.filled)
    (hYP : piece (agPocketY G) ⊆ P.filled) {vx vy : ℝ} (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2)
    (hy1 : 1 / 2 ≤ vy) (hy2 : vy ≤ 2) (hyA : inPt (G + 210) vy ∈ A) :
    ∀ p ∈ piece (agPocketY G), P.Sees (agI G vx vy) p ∨ P.Sees (inPt (G + 210) vy) p := by
  intro p hp
  obtain ⟨c1, c2, c3, c4⟩ := agPocketY_ccw (G := G)
  have hy0 : (0 : ℝ) ≤ vy := by linarith
  have hIf := agI_fst (G := G) hx2 hy0
  have hI := agI_mem_auxRegion (G := G) hx1 hx2 hy1 hy2
  obtain ⟨q0, q1, q2, q3⟩ := mem_piece_quad.1 hp
  simp only [det, agYlo, agN3, agR, agYhi] at q0 q1 q2 q3
  have hpd : p.1 ≤ G + 50 := by nlinarith
  have hpl : p.1 = G + 50 → -94 ≤ p.2 ∧ p.2 ≤ -77 := fun h => by
    rw [h] at q0 q2; constructor <;> linarith
  have hp2 : p.2 < -1 := by nlinarith
  have hmR : ∀ q : Point, q.1 = G + 50 → -94 ≤ q.2 → q.2 ≤ -77 → q ∈ piece (agRoom G) :=
    fun q h1 h2 h3 => agRoom_left h1 h2 (by linarith)
  have hmC : segment ((G + 50, -94) : Point) (G + 50, -77) ⊆ piece (agPocketY G) :=
    add_mouth_subset c1 c2 c3 c4
  have hS := ag_shadows_mem hy1 hy2
  have hN3 := agI_N3 (G := G) hx1 hx2 hy1 hy2
  have hRin := ag_input_y_R (G := G) (v := vy) hy2
  have hIR := agI_R (G := G) hx2 hy0
  have hgN : (agN3 G).1 < (inPt (G + 210) vy).1 := by simp only [agN3, inPt_fst]; linarith
  have hlh : (agYlo G).2 < (agYhi G).2 := by simp only [agYlo, agYhi]; norm_num
  have hc : G + 30 < (agN3 G).1 := by simp only [agN3]; linarith
  have hs1 : (agYlo G).2 ≤ vproj (inPt (G + 210) vy) (agN3 G) (G + 30) := by
    rw [ag_shadow_y]; exact hS.2.1.1.le
  have ha_lo : 0 ≤ det (inPt (G + 210) vy) (agR G) (agYlo G) :=
    add_det_vert_nonneg (c := G + 30) (h := -855 / 8) hgN (by linarith)
  have ha_dn : 0 ≤ det (inPt (G + 210) vy) (agR G) (agN3 G) := by
    simp only [det, agR, agN3, inPt_fst, inPt_snd]; nlinarith
  have ha_hi : 0 ≤ det (inPt (G + 210) vy) (agR G) (agYhi G) :=
    add_det_vert_nonneg (c := G + 30) (h := -423 / 4) hgN (by linarith)
  have hb_lo : det (agI G vx vy) (agN3 G) (agYlo G) ≤ 0 :=
    add_det_vert_nonpos (c := G + 30) (h := -855 / 8) hIf (by linarith)
  have hb_up : det (agI G vx vy) (agN3 G) (agR G) ≤ 0 := by
    simp only [det, agN3, agR]; nlinarith
  have hb_hi : det (agI G vx vy) (agN3 G) (agYhi G) ≤ 0 :=
    add_det_vert_nonpos (c := G + 30) (h := -423 / 4) hIf (by linarith)
  have hb_lo' : 0 ≤ det (agI G vx vy) (agR G) (agYlo G) :=
    add_det_vert_nonneg (c := G + 30) (h := -855 / 8) hIf (by rw [hIR]; exact hS.2.1.1.le)
  have hb_dn' : 0 ≤ det (agI G vx vy) (agR G) (agN3 G) := by
    simp only [det, agR, agN3]; nlinarith
  have hb_s : 0 ≤ det (agI G vx vy) (agR G)
      (G + 30, vproj (inPt (G + 210) vy) (agN3 G) (G + 30)) :=
    add_det_vert_nonneg hIf (by rw [hIR, ag_shadow_y])
  rcases add_pocket_split (lo := agYlo G) (dn := agN3 G) (up := agR G) (hi := agYhi G)
      (ga := inPt (G + 210) vy) (gb := agI G vx vy) (c := G + 30) c1 c3 c4 rfl rfl hlh hc hgN hs1
      ha_lo ha_dn ha_hi hb_lo hb_up hb_hi hb_lo' hb_dn' hb_s hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inr (add_sees_window_vmouth hA hAP (convex_piece _) hRP (convex_piece _) hYP
      (by linarith) (ag_window_mem hWA) (by norm_num) (by norm_num) hmR hmC hyA
      (by simp only [inPt_snd]; linarith) hgN hp hpd hpl hp2 ?_ ?_ h1 h2)
    · refine add_det_nonneg_quad c1 c3 hp ?_ ?_ ?_ ?_ <;>
        simp only [det, agYlo, agN3, agR, agYhi, inPt_fst, inPt_snd] <;> linarith
    · have sw : ∀ x, det ((G + 363, -1) : Point) (inPt (G + 210) vy) x =
          -det (inPt (G + 210) vy) (G + 363, -1) x := fun x => det_swap12 _ _ x
      have := add_det_nonneg_quad (A := ((G + 363, -1) : Point)) (B := inPt (G + 210) vy) c1 c3 hp
        (by simp only [det, agYlo, inPt_fst, inPt_snd]; linarith)
        (by simp only [det, agN3, inPt_fst, inPt_snd]; linarith)
        (by simp only [det, agR, inPt_fst, inPt_snd]; linarith)
        (by simp only [det, agYhi, inPt_fst, inPt_snd]; linarith)
      rw [sw] at this; linarith
  · exact Or.inl (add_sees_vmouth (convex_piece _) hRP (convex_piece _) hYP (by norm_num) hmR hmC
      hI.2 hIf hp hpd hpl h1 h2)

/-- A point of the z-pocket of `addGe` on the line of the mouth `[Q, N2]` lies on the mouth. -/
theorem ag_pocketZ_mouth {p : Point} (hp : p ∈ piece (agPocketZ G))
    (h0 : det (agQ G) (agN2 G) p = 0) : p ∈ segment (agQ G) (agN2 G) := by
  obtain ⟨c1, c2, c3, c4⟩ := agPocketZ_ccw (G := G)
  have hne : agQ G ≠ agN2 G := by
    intro h; have := congrArg Prod.fst h; simp only [agQ, agN2] at this; linarith
  obtain ⟨t, rfl⟩ := exists_lerp_of_det_eq_zero hne h0
  obtain ⟨q0, -, q2, -⟩ := mem_piece_quad.1 hp
  have e0 : det (agZlo G) (agQ G) (agQ G) = 0 := add_det_self _ _
  have e2 : det (agN2 G) (agZhi G) (agN2 G) = 0 := by unfold det; ring
  rw [det_lerp, e0] at q0
  rw [det_lerp, e2] at q2
  refine lerp_mem_segment _ _ ?_ ?_
  · by_contra h; push Not at h; nlinarith
  · by_contra h; push Not at h
    rw [show det (agN2 G) (agZhi G) (agQ G) = det (agQ G) (agN2 G) (agZhi G) by
      unfold det; ring] at q2
    nlinarith

/-- **`addGe`, z-pocket (chords argument, through the bay).**  With the aux guard at
`I(v_x, v_y)`, the z-input at `v_z` and `v_z ≤ v_x + v_y`, every point of the z-pocket is seen
by one of them. -/
theorem ag_pocketZ_cover (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (agWL G) (agWR G) ⊆ A) (hRP : piece (agRoom G) ⊆ P.filled)
    (hBP : piece (agBay G) ⊆ P.filled) (hZP : piece (agPocketZ G) ⊆ P.filled) {vx vy vz : ℝ}
    (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy) (hy2 : vy ≤ 2) (hz1 : 1 / 2 ≤ vz)
    (hz2 : vz ≤ 2) (hzA : inPt (G + 185 / 2) vz ∈ A) (hrel : vz ≤ vx + vy) :
    ∀ p ∈ piece (agPocketZ G), P.Sees (agI G vx vy) p ∨ P.Sees (inPt (G + 185 / 2) vz) p := by
  intro p hp
  obtain ⟨c1, c2, c3, c4⟩ := agPocketZ_ccw (G := G)
  have hy0 : (0 : ℝ) ≤ vy := by linarith
  have hIf := agI_fst (G := G) hx2 hy0
  have hQN2 := (agI_pos (G := G) hx1 hx2 hy1 hy2).2.2.2.2.2.2
  have hdm : ∀ q : Point, det (agQ G) (agN2 G) q =
      2831 / 300 * (q.1 - G - 50) - 35 / 2 * q.2 - 5285 / 6 := fun q => by
    simp only [det, agQ, agN2]; ring
  have hmZ : segment (agQ G) (agN2 G) ⊆ piece (agPocketZ G) := add_mouth_subset c1 c2 c3 c4
  have hBay := isPiece_tri (agBay_ccw (G := G))
  have hmB : segment (agQ G) (agN2 G) ⊆ piece (agBay G) := fun q hq => by
    rw [segment_comm] at hq
    exact edge_subset_piece hBay (j := 1) (by simp [tri, Polygon.n])
      (by simpa [Polygon.edge, agBay, tri, Polygon.vtx, Polygon.n] using hq)
  -- a guard `g` with the cone conditions sees `p` if it sees the whole bay
  have through : ∀ g : Point, det (agQ G) (agN2 G) g < 0 →
      (∀ x ∈ piece (agBay G), P.Sees g x) → det g (agQ G) p * det g (agN2 G) p ≤ 0 →
      P.Sees g p := by
    intro g hg hgB hc
    obtain ⟨q0, q1, q2, q3⟩ := mem_piece_quad.1 hp
    rcases eq_or_lt_of_le q1 with h0 | hpos
    · exact hgB p (hmB (ag_pocketZ_mouth hp h0.symm))
    · obtain ⟨q, hq, hqp⟩ := add_cross hg hpos hc
      exact sees_of_mem_segment hqp (hgB q (hmB hq))
        (sees_of_convex (convex_piece _) hZP (hmZ hq) hp)
  have hIg : det (agQ G) (agN2 G) (agI G vx vy) < 0 := by rw [hdm]; linarith
  have hgg : det (agQ G) (agN2 G) (inPt (G + 185 / 2) vz) < 0 := by
    rw [hdm]; simp only [inPt_fst, inPt_snd]; linarith
  have hauxB := ag_aux_sees_bay (P := P) hRP hBP hx1 hx2 hy1 hy2
  have hinB := ag_input_sees_bay hA hAP hWA hRP hBP hz1 hz2 hzA
  have hS := ag_shadows_mem hz1 hz2
  have hIQ := agI_Q (G := G) hx2 hy0
  have hrel' := (agI_Q_le_iff (G := G) (vz := vz) hx2 hy0).2 hrel
  have hN2I := agI_N2 (G := G) hx1 hx2 hy1 hy2
  have hQin := ag_input_z_Q (G := G) (v := vz) (by linarith)
  have hgN : (agN2 G).1 < (agI G vx vy).1 := by simp only [agN2]; linarith
  have hgQ : (agQ G).1 < (inPt (G + 185 / 2) vz).1 := by simp only [agQ, inPt_fst]; linarith
  -- the aux guard: the whole pocket is below its line through `N2`
  have hA_up : 0 ≤ det (agI G vx vy) (agN2 G) p := by
    refine add_det_nonneg_quad c1 c3 hp
      (add_det_vert_nonneg (c := G + 30) (h := -6001 / 96) hgN (by linarith)) ?_
      (add_det_self _ _).ge (add_det_vert_nonneg (c := G + 30) (h := -5941 / 96) hgN hN2I)
    have e : det (agI G vx vy) (agN2 G) (agQ G) = -det (agQ G) (agN2 G) (agI G vx vy) := by
      unfold det; ring
    rw [e]; linarith
  -- the z-input: the whole pocket is above its line through `Q`
  have hB_dn : det (inPt (G + 185 / 2) vz) (agQ G) p ≤ 0 := by
    have sw : ∀ x, det (agQ G) (inPt (G + 185 / 2) vz) x =
        -det (inPt (G + 185 / 2) vz) (agQ G) x := fun x => det_swap12 _ _ x
    have v1 : det (inPt (G + 185 / 2) vz) (agQ G) (agZlo G) ≤ 0 :=
      add_det_vert_nonpos (c := G + 30) (h := -6001 / 96) hgQ hQin
    have v4 : det (inPt (G + 185 / 2) vz) (agQ G) (agZhi G) ≤ 0 :=
      add_det_vert_nonpos (c := G + 30) (h := -5941 / 96) hgQ (by linarith)
    have v3 : det (inPt (G + 185 / 2) vz) (agQ G) (agN2 G) ≤ 0 := by
      simp only [det, agQ, agN2, inPt_fst, inPt_snd]; linarith
    have := add_det_nonneg_quad (A := agQ G) (B := inPt (G + 185 / 2) vz) c1 c3 hp
      (by rw [sw]; linarith) (by rw [sw, add_det_self]; simp) (by rw [sw]; linarith)
      (by rw [sw]; linarith)
    rw [sw] at this; linarith
  by_cases hlo : -6001 / 96 ≤ vproj (agI G vx vy) (agQ G) (G + 30)
  · have hlh : (agZlo G).2 < (agZhi G).2 := by simp only [agZlo, agZhi]; norm_num
    have hc : G + 30 < (agQ G).1 := by simp only [agQ]; linarith
    have hgN2 : (agN2 G).1 < (inPt (G + 185 / 2) vz).1 := by simp only [agN2, inPt_fst]; linarith
    rcases add_pocket_split (lo := agZlo G) (dn := agQ G) (up := agN2 G) (hi := agZhi G)
        (ga := agI G vx vy) (gb := inPt (G + 185 / 2) vz) (c := G + 30) c1 c3 c4 rfl rfl hlh hc
        hIf hlo
        (add_det_vert_nonneg (c := G + 30) (h := -6001 / 96) hgN (by linarith))
        (by
          have e : det (agI G vx vy) (agN2 G) (agQ G) =
              -det (agQ G) (agN2 G) (agI G vx vy) := by unfold det; ring
          rw [e]; linarith)
        (add_det_vert_nonneg (c := G + 30) (h := -5941 / 96) hgN hN2I)
        (add_det_vert_nonpos (c := G + 30) (h := -6001 / 96) hgQ hQin)
        (by simp only [det, agQ, agN2, inPt_fst, inPt_snd]; linarith)
        (add_det_vert_nonpos (c := G + 30) (h := -5941 / 96) hgQ (by linarith))
        (add_det_vert_nonneg (c := G + 30) (h := -6001 / 96) hgN2
          (by rw [ag_shadow_z]; exact hS.2.2.1))
        (by simp only [det, agN2, agQ, inPt_fst, inPt_snd]; linarith)
        (add_det_vert_nonneg hgN2 (by rw [ag_shadow_z]; exact hrel')) hp with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (through _ hIg hauxB (mul_nonpos_of_nonpos_of_nonneg h1 h2))
    · exact Or.inr (through _ hgg hinB (mul_nonpos_of_nonpos_of_nonneg h1 h2))
  · -- the shadow of the aux guard through `Q` is below the nook: it sees the whole pocket
    push Not at hlo
    left
    have hA_dn : det (agI G vx vy) (agQ G) p ≤ 0 := by
      have sw : ∀ x, det (agQ G) (agI G vx vy) x = -det (agI G vx vy) (agQ G) x :=
        fun x => det_swap12 _ _ x
      have v1 : det (agI G vx vy) (agQ G) (agZlo G) ≤ 0 :=
        add_det_vert_nonpos (c := G + 30) (h := -6001 / 96) hIf hlo.le
      have v4 : det (agI G vx vy) (agQ G) (agZhi G) ≤ 0 :=
        add_det_vert_nonpos (c := G + 30) (h := -5941 / 96) hIf (by linarith)
      have v3 : det (agI G vx vy) (agQ G) (agN2 G) ≤ 0 := by
        have e : det (agI G vx vy) (agQ G) (agN2 G) = det (agQ G) (agN2 G) (agI G vx vy) := by
          unfold det; ring
        rw [e]; linarith
      have := add_det_nonneg_quad (A := agQ G) (B := agI G vx vy) c1 c3 hp
        (by rw [sw]; linarith) (by rw [sw, add_det_self]; simp) (by rw [sw]; linarith)
        (by rw [sw]; linarith)
      rw [sw] at this; linarith
    exact through _ hIg hauxB (mul_nonpos_of_nonpos_of_nonneg hA_dn hA_up)

/-- **`addGe`: the aux guard sees the room** (any point of the room). -/
theorem ag_aux_sees_room (hRP : piece (agRoom G) ⊆ P.filled) {g : Point}
    (hg : g ∈ piece (agRoom G)) : ∀ x ∈ piece (agRoom G), P.Sees g x :=
  fun _ hx => sees_of_convex (convex_piece _) hRP hg hx

/-- **`addGe`: the aux guard sees the aux wedge** (any point of the aux region strictly above
the bottom of the room, e.g. the canonical point). -/
theorem ag_aux_sees_auxTri (hRP : piece (agRoom G) ⊆ P.filled)
    (hTP : piece (agAuxTri G) ⊆ P.filled) {g : Point} (hg : g ∈ agAuxRegion G)
    (hg2 : -94 < g.2) : ∀ x ∈ piece (agAuxTri G), P.Sees g x := by
  intro x hx
  obtain ⟨⟨k1, k2⟩, hgR⟩ := hg
  have htri : 0 < det (agM1 G) (agTip G) (agM2 G) := by
    simp only [det, agM1, agTip, agM2]; linarith
  refine add_sees_tri_through htri (convex_piece _) hRP hTP hgR ?_ ?_ ?_ ?_ hx
  · intro q hq
    rw [segment_comm] at hq
    obtain ⟨h1, h2, h3⟩ :=
      (mem_segment_horiz_iff (c := -94) (x₁ := G + 327 / 4) (x₂ := G + 329 / 4) (by linarith)).1 hq
    exact mem_agRoom.2 ⟨by rw [h1]; linarith, by linarith, by linarith, by linarith,
      by linarith⟩
  · simp only [det, agM2, agM1]; nlinarith
  · have e : det g (agM2 G) (agTip G) = -det (agTip G) (agM2 G) g := by unfold det; ring
    rw [e]; linarith
  · have e : det g (agM1 G) (agTip G) = det (agM1 G) (agTip G) g := by unfold det; ring
    rw [e]; exact k1

/-- `addGe`: the needle of the z-input hanging from the bottom of the room. -/
noncomputable def agNeedleZ (G H : ℝ) : Polygon :=
  tri (G + 185 / 2, -94) (G + 185 / 2, -94 - H) (G + 371 / 4, -94)

/-- `addGe`: the needle of the y-input hanging from the bottom of the room. -/
noncomputable def agNeedleY (G H : ℝ) : Polygon :=
  tri (G + 210, -94) (G + 210, -94 - H) (G + 841 / 4, -94)

/-- An input standing above the window sees its needle hanging from the bottom of the room
(generic form for `addGe`, needle at abscissa `G + δ`, `85 ≤ δ ≤ 362`). -/
theorem ag_needle_seen {δ δ' H : ℝ} (hδ1 : 85 ≤ δ) (hδ2 : δ ≤ 362) (hδ' : δ' = δ + 1 / 4)
    (hH : 0 < H) (hA : Convex ℝ A) (hAP : A ⊆ P.filled) (hWA : segment (agWL G) (agWR G) ⊆ A)
    (hRP : piece (agRoom G) ⊆ P.filled)
    (hTP : piece (tri (G + δ, -94) (G + δ, -94 - H) (G + δ', -94)) ⊆ P.filled)
    {v : ℝ} (hv1 : 1 / 2 ≤ v) (_hv2 : v ≤ 2) (hgA : inPt (G + δ) v ∈ A) :
    ∀ x ∈ piece (tri (G + δ, -94) (G + δ, -94 - H) (G + δ', -94)),
      P.Sees (inPt (G + δ) v) x := by
  subst hδ'
  intro x hx
  set g := inPt (G + δ) v with hg
  have htri : 0 < det ((G + δ, -94) : Point) (G + δ, -94 - H) (G + (δ + 1 / 4), -94) := by
    simp only [det]; linarith
  obtain ⟨t0, t1, t2⟩ := mem_piece_tri.1 hx
  simp only [det] at t0 t1 t2
  have hx2 : x.2 ≤ -94 := by nlinarith
  have hx1 : G + δ ≤ x.1 := by nlinarith
  have hx1' : x.1 ≤ G + δ + 1 / 4 := by
    by_contra hc; push Not at hc; nlinarith [mul_pos hH (by linarith : (0 : ℝ) < x.1 - G - δ - 1 / 4)]
  have hw1 : 0 ≤ det g (G + 85, -1) x := by
    refine add_det_nonneg_tri htri hx ?_ ?_ ?_ <;> simp only [det, hg, inPt_fst, inPt_snd] <;>
      nlinarith
  have hw2 : det g (G + 363, -1) x ≤ 0 := by
    have sw : ∀ y, det ((G + 363, -1) : Point) g y = -det g (G + 363, -1) y :=
      fun y => det_swap12 _ _ y
    have := add_det_nonneg_tri (A := ((G + 363, -1) : Point)) (B := g) htri hx
      (by rw [sw]; simp only [det, hg, inPt_fst, inPt_snd]; nlinarith)
      (by rw [sw]; simp only [det, hg, inPt_fst, inPt_snd]; nlinarith)
      (by rw [sw]; simp only [det, hg, inPt_fst, inPt_snd]; nlinarith)
    rw [sw] at this; linarith
  obtain ⟨q, hq, e1, e2, e3⟩ := add_cross_window (by linarith)
    (by simp only [hg, inPt_snd]; linarith) (by linarith) hw1 hw2
  obtain ⟨hqA, hqR⟩ := ag_window_mem hWA q e1 e2 e3
  have hq1 : G + δ ≤ q.1 ∧ q.1 ≤ G + δ + 1 / 4 := by
    obtain ⟨l, hl0, hl1, rfl⟩ := mem_segment_iff_lerp.1 hq
    simp only [lerp_fst, hg, inPt_fst]
    constructor <;> nlinarith
  refine sees_of_mem_segment hq (sees_of_convex hA hAP hgA hqA) ?_
  refine add_sees_tri_through htri (convex_piece _) hRP hTP hqR ?_ ?_ ?_ ?_ hx
  · intro y hy
    rw [segment_comm] at hy
    obtain ⟨h1, h2, h3⟩ :=
      (mem_segment_horiz_iff (c := -94) (x₁ := G + δ) (x₂ := G + (δ + 1 / 4)) (by linarith)).1 hy
    exact mem_agRoom.2 ⟨by rw [h1]; linarith, by linarith, by linarith, by linarith,
      by linarith⟩
  · simp only [det]; rw [e1]; linarith
  · simp only [det]; rw [e1]
    nlinarith [mul_nonneg hH.le (by linarith : (0 : ℝ) ≤ G + δ + 1 / 4 - q.1)]
  · simp only [det]; rw [e1]; nlinarith [mul_nonneg hH.le (by linarith : (0 : ℝ) ≤ q.1 - G - δ)]

/-- **`addGe`: the z-input sees its needle.** -/
theorem ag_needleZ_seen {H : ℝ} (hH : 0 < H) (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (agWL G) (agWR G) ⊆ A) (hRP : piece (agRoom G) ⊆ P.filled)
    (hTP : piece (agNeedleZ G H) ⊆ P.filled) {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hgA : inPt (G + 185 / 2) v ∈ A) :
    ∀ x ∈ piece (agNeedleZ G H), P.Sees (inPt (G + 185 / 2) v) x :=
  ag_needle_seen (δ := 185 / 2) (δ' := 371 / 4) (by norm_num) (by norm_num) (by norm_num) hH hA
    hAP hWA hRP hTP hv1 hv2 hgA

/-- **`addGe`: the y-input sees its needle.** -/
theorem ag_needleY_seen {H : ℝ} (hH : 0 < H) (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (agWL G) (agWR G) ⊆ A) (hRP : piece (agRoom G) ⊆ P.filled)
    (hTP : piece (agNeedleY G H) ⊆ P.filled) {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hgA : inPt (G + 210) v ∈ A) : ∀ x ∈ piece (agNeedleY G H), P.Sees (inPt (G + 210) v) x :=
  ag_needle_seen (δ := 210) (δ' := 841 / 4) (by norm_num) (by norm_num) (by norm_num) hH hA
    hAP hWA hRP hTP hv1 hv2 hgA

end Stade

end ArtGallery

end
