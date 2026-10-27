module

public import ArtGallery.Stade.GuardAdd
public import ArtGallery.Stade.AdditionGeomGe

/-!
# The canonical guards see the addition gadget `addGe` (proof plan L7.7, L7.8)

`addGe` (slot origin `G`, needle depth `H`): with the aux guard at the canonical point
`agI G v_x v_y` and the input guards at the values of the variables, every point of the room,
the bay `N1 N2 Q`, the three pockets, the aux wedge and the two needles hanging from the room
bottom is seen by one of the four guards, provided `v_z ≤ v_x + v_y` (`ag_slot_cover`).  Both the
aux guard and the z-input see the whole bay (through its door `[Q, N1]` on the room's left side),
hence the whole slanted mouth `[Q, N2]` of the z-pocket.
-/

@[expose] public section

namespace ArtGallery.Stade

variable {P : Polygon} {G : ℝ}

/-- `addGe`: a guard in `A` above the window, weakly left of the right wall and right of the
upper-left wall line, sees every point of the room. -/
theorem ag_room_sees {A : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (agWL G) (agWR G) ⊆ A) (hRP : piece (agRoom G) ⊆ P.filled) {g : Point}
    (hgA : g ∈ A) (h1 : g.1 ≤ G + 363) (h2 : 0 ≤ 36 * (g.1 - G - 50) - 35 * g.2 - 1295)
    (h3 : -1 ≤ g.2) : ∀ z ∈ piece (agRoom G), P.Sees g z := by
  intro z hz
  obtain ⟨q, hq, hqz⟩ := cross_pent (a := agWL G) (b := agP G) (c := agN3 G) (d := agBR G)
    (e := agWR G) (g := g) (by simp only [det, agBR, agWR, agWL]; linarith)
    (by simp only [det, agWR, agWL, agP]; linarith)
    (by simp only [det, agWL, agP]; linarith) (by simp only [det, agBR, agWR]; nlinarith)
    (by simp only [det, agWR, agWL]; nlinarith) hz
  rw [Geometry.segment_comm] at hq
  exact sees_of_two_convex hA (convex_piece _) hAP hRP hgA hz (hWA hq) (agRoom_window hq) hqz

/-- `addGe`: the x-input (right of the window) sees the mouth `[N1, P]` of the x-pocket, through
the window and the sub-quadrilateral `WL, P, N1, WR` of the room. -/
theorem ag_xmouth_sees {A : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (agWL G) (agWR G) ⊆ A) (hRP : piece (agRoom G) ⊆ P.filled) {v : ℝ}
    (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) (hgA : inPt (G + 370) v ∈ A) :
    ∀ m ∈ segment (agN1 G) (agP G), P.Sees (inPt (G + 370) v) m := by
  intro m hm
  set g := inPt (G + 370) v with hg
  have hg1 : g.1 = G + 370 := rfl
  have hg2 : g.2 = 4 * v - 2 := rfl
  set K := quad (agWL G) (agP G) (agN1 G) (agWR G) with hK
  have hKR : piece K ⊆ piece (agRoom G) := by
    intro x hx
    obtain ⟨k1, k2, k3, k4⟩ := mem_piece_quad.1 hx
    simp only [det, agWL, agP, agN1, agWR] at k1 k2 k3 k4
    exact mem_agRoom.2 ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hmK : m ∈ piece K := by
    have hc := convex_piece K
    have h1 : agN1 G ∈ piece K := by
      refine mem_piece_quad.2 ⟨?_, ?_, ?_, ?_⟩ <;> simp only [det, agWL, agP, agN1, agWR] <;>
        linarith
    have h2 : agP G ∈ piece K := by
      refine mem_piece_quad.2 ⟨?_, ?_, ?_, ?_⟩ <;> simp only [det, agWL, agP, agN1, agWR] <;>
        linarith
    exact Geometry.segment_subset_of_convex hc h1 h2 hm
  obtain ⟨q, hq, hqm⟩ := cross_quad (a := agWL G) (b := agP G) (c := agN1 G) (d := agWR G)
    (g := g) (by simp only [det, agN1, agWR, agWL]; linarith)
    (by simp only [det, agWR, agWL, agP]; linarith)
    (by simp only [det, agWL, agP]; rw [hg1, hg2]; nlinarith)
    (by simp only [det, agN1, agWR]; rw [hg1, hg2]; nlinarith)
    (by simp only [det, agWR, agWL]; rw [hg2]; nlinarith) hmK
  rw [Geometry.segment_comm] at hq
  exact sees_of_two_convex hA (convex_piece _) hAP hRP hgA (hKR hmK) (hWA hq) (agRoom_window hq)
    hqm

/-- `addGe`: a guard that sees every point of the door `[Q, N1]` of the bay and lies weakly left
of the bay sides `N1 N2`, `N2 Q` and right of `x = G + 50` sees every point of the bay. -/
theorem ag_bay_sees (hBP : piece (agBay G) ⊆ P.filled) {g : Point}
    (h1 : 0 ≤ det (agN1 G) (agN2 G) g) (h2 : 0 ≤ det (agN2 G) (agQ G) g) (h3 : G + 50 ≤ g.1)
    (hdoor : ∀ q ∈ segment (agQ G) (agN1 G), P.Sees g q) :
    ∀ z ∈ piece (agBay G), P.Sees g z := by
  intro z hz
  obtain ⟨q, hq, hqz⟩ := cross_tri (agBay_ccw (G := G)) h1 h2
    (by simp only [det, agQ, agN1]; nlinarith) hz
  have hqB : q ∈ piece (agBay G) := by
    have := edge_subset_piece (isPiece_tri (agBay_ccw (G := G))) (j := 2) (by simp [tri_n])
    rw [(tri_edge _ _ _).2.2] at this
    exact this hq
  exact sees_via (convex_piece _) hBP hqz (hdoor q hq) hqB hz

/-- The z-needle of `addGe` (hanging from the room bottom `y = −94` at `G + 185/2`). -/
noncomputable def agHungZ (G H : ℝ) : Polygon := needleR (G + 185 / 2) (-94) H

/-- The y-needle of `addGe` (hanging from the room bottom at `G + 210`). -/
noncomputable def agHungY (G H : ℝ) : Polygon := needleR (G + 210) (-94) H

/-- The pieces of an `addGe` slot below the floor (except the floor needle of the x-input). -/
noncomputable def agPieces (G H : ℝ) : List Polygon :=
  [agRoom G, agBay G, agPocketX G, agPocketY G, agPocketZ G, agAuxTri G, agHungZ G H,
    agHungY G H]

/-- **`addGe` slot coverage (L7.8).**  `A` (the hall) is a convex part of the region containing
the window and the input guards; the pieces of the slot lie in the region; the walls of the
pockets are edges of `P`.  If all values are in `[1/2, 2]` and `v_z ≤ v_x + v_y`, every point
of every piece is seen by the aux guard `agI G v_x v_y` or one of the input guards. -/
theorem ag_slot_cover (hP : P.Simple) (hL : P.InteriorLeft) (hW : AgWalls P G) {A : Set Point}
    (hA : Convex ℝ A) (hAP : A ⊆ P.filled) (hWA : segment (agWL G) (agWR G) ⊆ A) {H : ℝ}
    (hH : 0 < H) (hKP : ∀ K ∈ agPieces G H, piece K ⊆ P.filled) {vx vy vz : ℝ}
    (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy) (hy2 : vy ≤ 2) (hz1 : 1 / 2 ≤ vz)
    (hz2 : vz ≤ 2) (hrel : vz ≤ vx + vy)
    (hxA : inPt (G + 370) vx ∈ A) (hyA : inPt (G + 210) vy ∈ A)
    (hzA : inPt (G + 185 / 2) vz ∈ A) :
    ∀ K ∈ agPieces G H, ∀ z ∈ piece K, ∃ g ∈ ({agI G vx vy, inPt (G + 370) vx,
      inPt (G + 210) vy, inPt (G + 185 / 2) vz} : Set Point), P.Sees g z := by
  have hRP := hKP (agRoom G) (by simp [agPieces])
  have hBP := hKP (agBay G) (by simp [agPieces])
  have hXP := hKP (agPocketX G) (by simp [agPieces])
  have hYP := hKP (agPocketY G) (by simp [agPieces])
  have hZP := hKP (agPocketZ G) (by simp [agPieces])
  have hTP := hKP (agAuxTri G) (by simp [agPieces])
  have hNZ := hKP (agHungZ G H) (by simp [agPieces])
  have hNY := hKP (agHungY G H) (by simp [agPieces])
  have hI := agI_mem_auxRegion (G := G) hx1 hx2 hy1 hy2
  have hIb := ag_aux_bounds (G := G) (Or.inr hI)
  have hIf := agI_fst (G := G) (vx := vx) (vy := vy) hx2 (by linarith)
  have hIQN2 := (agI_pos (G := G) hx1 hx2 hy1 hy2).2.2.2.2.2.2
  obtain ⟨hcov1, hcov2, hcov3⟩ := ag_cover_of_rel hA hAP hWA hRP hBP hXP hYP hZP hx1 hx2 hy1 hy2
    hz1 hz2 hxA hyA hzA hrel
  have hIR := hI.2
  have hIR' := mem_agRoom.1 hIR
  -- the aux guard sees the room
  have hauxR : ∀ z ∈ piece (agRoom G), P.Sees (agI G vx vy) z := fun z hz =>
    sees_of_convex (convex_piece _) hRP hIR hz
  -- the y- and z-inputs see the room
  have hyR : ∀ z ∈ piece (agRoom G), P.Sees (inPt (G + 210) vy) z :=
    ag_room_sees hA hAP hWA hRP hyA (by simp only [inPt_fst]; linarith)
      (by simp only [inPt_fst, inPt_snd]; nlinarith) (by simp only [inPt_snd]; linarith)
  have hzR : ∀ z ∈ piece (agRoom G), P.Sees (inPt (G + 185 / 2) vz) z :=
    ag_room_sees hA hAP hWA hRP hzA (by simp only [inPt_fst]; linarith)
      (by simp only [inPt_fst, inPt_snd]; nlinarith) (by simp only [inPt_snd]; linarith)
  have hseg : ∀ (y₁ y₂ : ℝ), y₁ ≤ y₂ → -94 ≤ y₁ → y₂ ≤ -37 →
      ∀ q ∈ segment ((G + 50, y₁) : Point) (G + 50, y₂), q ∈ piece (agRoom G) := by
    intro y₁ y₂ hy hy1 hy2 q hq
    obtain ⟨e1, e2, e3⟩ := (mem_segment_vert_iff hy).1 hq
    exact agRoom_left e1 (by linarith) (by linarith)
  have hdoorR : ∀ q ∈ segment (agQ G) (agN1 G), q ∈ piece (agRoom G) := fun q hq =>
    hseg (-151 / 3) (-153 / 4) (by norm_num) (by norm_num) (by norm_num) q
      (by simpa only [agQ, agN1] using hq)
  -- both the aux guard and the z-input see the bay
  have hauxB : ∀ z ∈ piece (agBay G), P.Sees (agI G vx vy) z :=
    ag_bay_sees hBP (by simp only [det, agN1, agN2]; linarith)
      (by simp only [det, agN2, agQ]; linarith) hIf.le (fun q hq => hauxR q (hdoorR q hq))
  have hzB : ∀ z ∈ piece (agBay G), P.Sees (inPt (G + 185 / 2) vz) z :=
    ag_bay_sees hBP (by simp only [det, agN1, agN2, inPt_fst, inPt_snd]; nlinarith)
      (by simp only [det, agN2, agQ, inPt_fst, inPt_snd]; nlinarith)
      (by simp only [inPt_fst]; linarith) (fun q hq => hzR q (hdoorR q hq))
  have hmB : segment (agQ G) (agN2 G) ⊆ piece (agBay G) := fun q hq => by
    have := edge_subset_piece (isPiece_tri (agBay_ccw (G := G))) (j := 1) (by simp [tri_n])
    rw [(tri_edge _ _ _).2.1, Geometry.segment_comm] at this
    exact this hq
  have houtI : ∀ (lo dn up hi : Point), dn.1 = up.1 → dn.2 < up.2 → dn.1 = G + 50 →
      agI G vx vy ∉ piece (quad lo dn up hi) := fun lo dn up hi hd hdu h50 =>
    add_not_mem_pocket hd hdu (by rw [h50]; exact hIf)
  have houtIn : ∀ (lo dn up hi : Point) (g : Point), dn.1 = up.1 → dn.2 < up.2 →
      dn.1 = G + 50 → G + 50 < g.1 → g ∉ piece (quad lo dn up hi) :=
    fun lo dn up hi g hd hdu h50 hg => add_not_mem_pocket hd hdu (by rw [h50]; exact hg)
  intro K hK z hz
  simp only [agPieces, List.mem_cons, List.mem_nil_iff, or_false] at hK
  rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- room
    exact ⟨_, Or.inl rfl, hauxR z hz⟩
  · -- bay
    exact ⟨_, Or.inl rfl, hauxB z hz⟩
  · -- x-pocket
    obtain ⟨c1, c2, c3, c4⟩ := agPocketX_ccw (G := G)
    have := pocket_cover_of_sees hP hL c1 c2 c3 c4 hW.x0 hW.x2 hW.x3 hXP
      (Gs := {agI G vx vy, inPt (G + 370) vx})
      (fun g hg m hm => by
        rcases hg with rfl | rfl
        · exact hauxR m (hseg (-153 / 4) (-37) (by norm_num) (by norm_num) (by norm_num) m
            (by simpa only [agN1, agP] using hm))
        · exact ag_xmouth_sees hA hAP hWA hRP hx1 hx2 hxA m hm)
      (fun g hg => by
        rcases hg with rfl | rfl
        · exact houtI _ _ _ _ (by simp [agN1, agP]) (by simp only [agN1, agP]; norm_num)
            (by simp [agN1])
        · exact houtIn _ _ _ _ _ (by simp [agN1, agP]) (by simp only [agN1, agP]; norm_num)
            (by simp [agN1]) (by simp only [inPt_fst]; linarith))
      (fun s hs => (hcov1 s hs).elim (fun h => ⟨_, Or.inl rfl, h⟩)
        (fun h => ⟨_, Or.inr rfl, h⟩)) z hz
    obtain ⟨g, hg, hgz⟩ := this
    rcases hg with rfl | rfl
    · exact ⟨_, Or.inl rfl, hgz⟩
    · exact ⟨_, Or.inr (Or.inl rfl), hgz⟩
  · -- y-pocket
    obtain ⟨c1, c2, c3, c4⟩ := agPocketY_ccw (G := G)
    have := pocket_cover_of_sees hP hL c1 c2 c3 c4 hW.y0 hW.y2 hW.y3 hYP
      (Gs := {agI G vx vy, inPt (G + 210) vy})
      (fun g hg m hm => by
        have hmR := hseg (-94) (-77) (by norm_num) (by norm_num) (by norm_num) m
          (by simpa only [agN3, agR] using hm)
        rcases hg with rfl | rfl
        · exact hauxR m hmR
        · exact hyR m hmR)
      (fun g hg => by
        rcases hg with rfl | rfl
        · exact houtI _ _ _ _ (by simp [agN3, agR]) (by simp only [agN3, agR]; norm_num)
            (by simp [agN3])
        · exact houtIn _ _ _ _ _ (by simp [agN3, agR]) (by simp only [agN3, agR]; norm_num)
            (by simp [agN3]) (by simp only [inPt_fst]; linarith))
      (fun s hs => (hcov2 s hs).elim (fun h => ⟨_, Or.inl rfl, h⟩)
        (fun h => ⟨_, Or.inr rfl, h⟩)) z hz
    obtain ⟨g, hg, hgz⟩ := this
    rcases hg with rfl | rfl
    · exact ⟨_, Or.inl rfl, hgz⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), hgz⟩
  · -- z-pocket
    obtain ⟨c1, c2, c3, c4⟩ := agPocketZ_ccw (G := G)
    have := pocket_cover_of_sees hP hL c1 c2 c3 c4 hW.z0 hW.z2 hW.z3 hZP
      (Gs := {agI G vx vy, inPt (G + 185 / 2) vz})
      (fun g hg m hm => by
        rcases hg with rfl | rfl
        · exact hauxB m (hmB hm)
        · exact hzB m (hmB hm))
      (fun g hg => by
        rcases hg with rfl | rfl
        · exact ag_not_mem_pocketZ hIf
        · exact ag_not_mem_pocketZ (by simp only [inPt_fst]; linarith))
      (fun s hs => (hcov3 s hs).elim (fun h => ⟨_, Or.inl rfl, h⟩)
        (fun h => ⟨_, Or.inr rfl, h⟩)) z hz
    obtain ⟨g, hg, hgz⟩ := this
    rcases hg with rfl | rfl
    · exact ⟨_, Or.inl rfl, hgz⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), hgz⟩
  · -- aux wedge
    obtain ⟨⟨k1, k2⟩, -⟩ := hI
    refine ⟨_, Or.inl rfl, wedge_sees (convex_piece _) hRP (a := agM1 G) (b := agTip G)
      (c := agM2 G) (by simp only [det, agM1, agTip, agM2]; norm_num) k1 k2
      (by simp only [det, agM2, agM1]; nlinarith) hIR ?_ hTP z hz⟩
    intro q hq
    obtain ⟨e1, e2, e3⟩ := (mem_segment_horiz_iff (c := -94) (x₁ := G + 327 / 4)
      (x₂ := G + 329 / 4) (by linarith)).1
      (by rw [Geometry.segment_comm]; simpa only [agM1, agM2] using hq)
    exact mem_agRoom.2 ⟨by nlinarith, by linarith, by linarith, by linarith, by linarith⟩
  · -- z-needle
    refine ⟨_, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
    refine needleR_sees_via (s := G + 185 / 2) (y := 4 * vz - 2) hH (by linarith)
      (fun q hq => ?_) hNZ z hz
    obtain ⟨e1, e2, e3⟩ := (mem_segment_horiz_iff (c := -94) (x₁ := G + 185 / 2)
      (x₂ := G + 185 / 2 + 1 / 4) (by linarith)).1 (by rw [Geometry.segment_comm]; exact hq)
    exact hzR q (mem_agRoom.2 ⟨by nlinarith, by linarith, by linarith, by linarith, by linarith⟩)
  · -- y-needle
    refine ⟨_, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
    refine needleR_sees_via (s := G + 210) (y := 4 * vy - 2) hH (by linarith) (fun q hq => ?_)
      hNY z hz
    obtain ⟨e1, e2, e3⟩ := (mem_segment_horiz_iff (c := -94) (x₁ := G + 210)
      (x₂ := G + 210 + 1 / 4) (by linarith)).1 (by rw [Geometry.segment_comm]; exact hq)
    exact hyR q (mem_agRoom.2 ⟨by nlinarith, by linarith, by linarith, by linarith, by linarith⟩)

end ArtGallery.Stade

end
