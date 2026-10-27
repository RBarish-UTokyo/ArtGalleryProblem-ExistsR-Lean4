module

public import ArtGallery.Stade.GuardWedges
public import ArtGallery.Stade.AdditionGeom

/-!
# The canonical guards see the addition gadget `addLe` (proof plan L7.8)

Generic tools:
* `pocket_cross_of_sees`: a guard outside a pocket (whose walls are edges of `P`) that sees a
  point of the pocket sees it through the mouth (room lemma);
* `pocket_cover_of_sees`: hence a pocket whose nook is covered by guards seeing the whole mouth
  is seen entirely (`pocket_cover`);
* `cross_pent`: crossing the door of a pentagon.

`addLe` (slot origin `G`, needle depth `H`): with the aux guard at the canonical point
`alI G v_x v_y` and the input guards at the values of the variables, every point of the room, of
the three pockets, of the aux wedge and of the two needles hanging from the room bottom is seen
by one of the four guards (`al_slot_cover`), provided `v_x + v_y ≤ v_z ≤ 2`.
-/

@[expose] public section

namespace ArtGallery.Stade

variable {P : Polygon}

/-! ### Generic tools -/

section Generic

variable {lo dn up hi : Point}

/-- A guard outside a pocket whose walls `lo → dn`, `up → hi`, `hi → lo` are edges of `P`, seeing
a point of the pocket, sees it through the mouth `[dn, up]`. -/
theorem pocket_cross_of_sees (hP : P.Simple) (hL : P.InteriorLeft) (h1 : 0 < det lo dn up)
    (h2 : 0 < det dn up hi) (h3 : 0 < det up hi lo) (h4 : 0 < det hi lo dn)
    (w0 : PEdge P lo dn) (w2 : PEdge P up hi) (w3 : PEdge P hi lo) {g s : Point}
    (hg : g ∉ piece (quad lo dn up hi)) (hs : s ∈ piece (quad lo dn up hi)) (h : P.Sees g s) :
    ∃ q ∈ segment dn up, q ∈ segment g s := by
  have hR := isRoom_piece hP hL (isPiece_quad h1 h2 h3 h4) (pocket_hWO w0 w2 w3)
  rw [door_quad_one] at hR
  obtain ⟨y, hyD, hy⟩ := Polygon.sees_crosses_door hR hs hg (Polygon.sees_comm.1 h)
  rw [Geometry.segment_comm] at hy
  exact ⟨y, hyD, hy⟩

/-- **Pocket coverage from nook coverage.**  If the nook `[lo, hi]` of a pocket (walls edges of
`P`, piece in the region) is covered by guards of `Gs` lying outside the pocket and seeing the
whole mouth, then every point of the pocket is seen by a guard of `Gs`. -/
theorem pocket_cover_of_sees (hP : P.Simple) (hL : P.InteriorLeft) (h1 : 0 < det lo dn up)
    (h2 : 0 < det dn up hi) (h3 : 0 < det up hi lo) (h4 : 0 < det hi lo dn)
    (w0 : PEdge P lo dn) (w2 : PEdge P up hi) (w3 : PEdge P hi lo)
    (hKP : piece (quad lo dn up hi) ⊆ P.filled) {Gs : Set Point}
    (hmouth : ∀ g ∈ Gs, ∀ m ∈ segment dn up, P.Sees g m)
    (hout : ∀ g ∈ Gs, g ∉ piece (quad lo dn up hi))
    (hnook : ∀ s ∈ segment lo hi, ∃ g ∈ Gs, P.Sees g s) :
    ∀ z ∈ piece (quad lo dn up hi), ∃ g ∈ Gs, P.Sees g z := by
  refine pocket_cover h1 h2 h3 h4 hKP hmouth (fun s hs => ?_)
  obtain ⟨g, hg, hgs⟩ := hnook s hs
  have hsK : s ∈ piece (quad lo dn up hi) := by
    have := edge_subset_piece (isPiece_quad h1 h2 h3 h4) (j := 3) (by simp [quad_n])
    rw [(quad_edge lo dn up hi).2.2.2, Geometry.segment_comm] at this
    exact this hs
  exact ⟨g, hg, pocket_cross_of_sees hP hL h1 h2 h3 h4 w0 w2 w3 (hout g hg) hsK hgs⟩

end Generic

/-- **Crossing the door of a pentagon.**  `a b c d e` a convex piece with strictly convex corners
at `e` and `a`; `g` weakly left of the sides `a b`, `d e` and weakly right of the door `e a`:
every segment from `g` to a point of the pentagon meets the door. -/
theorem cross_pent {a b c d e g z : Point} (hdea : 0 < det d e a) (heab : 0 < det e a b)
    (hg1 : 0 ≤ det a b g) (hg4 : 0 ≤ det d e g) (hg5 : det e a g ≤ 0)
    (hz : z ∈ piece (pent a b c d e)) : ∃ q ∈ segment e a, q ∈ segment g z := by
  obtain ⟨hz1, -, -, hz4, hz5⟩ := mem_piece_pent.1 hz
  obtain ⟨t, ht0, ht1, ht⟩ := exists_zero_on_segment hg5 hz5
  have hq := Geometry.lerp_mem_segment g z ht0 ht1
  exact ⟨_, mem_segment_of_side hdea heab ht (det_nonneg_of_mem_segment hq hg4 hz4)
    (det_nonneg_of_mem_segment hq hg1 hz1), hq⟩

/-! ### `addLe` -/

section addLe

variable {G : ℝ}

/-- The floor line of the slot lies in `A`: the window `[WL, WR]` lies in `A`. -/
theorem seg_floor_subset {A : Set Point} (hA : Convex ℝ A) {x₁ x₂ : ℝ}
    (hFA : ∀ x, x₁ ≤ x → x ≤ x₂ → ((x, -1) : Point) ∈ A) {u w : ℝ} (hu1 : x₁ ≤ u)
    (hu2 : u ≤ x₂) (hw1 : x₁ ≤ w) (hw2 : w ≤ x₂) :
    segment ((u, -1) : Point) (w, -1) ⊆ A :=
  Geometry.segment_subset_of_convex hA (hFA u hu1 hu2) (hFA w hw1 hw2)

/-- `addLe`: a guard in `A` above the window, weakly left of the right wall and right of the
upper-left wall line, sees every point of the room. -/
theorem al_room_sees {A : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (alWL G) (alWR G) ⊆ A) (hRP : piece (alRoom G) ⊆ P.filled) {g : Point}
    (hgA : g ∈ A) (h1 : g.1 ≤ G + 527) (h2 : 0 ≤ 441 / 4 * (g.1 - G - 50) - 150 * g.2 - 33375 / 2)
    (h3 : -1 ≤ g.2) : ∀ z ∈ piece (alRoom G), P.Sees g z := by
  intro z hz
  obtain ⟨q, hq, hqz⟩ := cross_pent (a := alWL G) (b := alN1 G) (c := alR G) (d := alBR G)
    (e := alWR G) (g := g) (by simp only [det, alBR, alWR, alWL]; linarith)
    (by simp only [det, alWR, alWL, alN1]; linarith)
    (by simp only [det, alWL, alN1]; linarith) (by simp only [det, alBR, alWR]; nlinarith)
    (by simp only [det, alWR, alWL]; nlinarith) hz
  rw [Geometry.segment_comm] at hq
  exact sees_of_two_convex hA (convex_piece _) hAP hRP hgA hz (hWA hq) (alRoom_window hq) hqz

/-- `addLe`: the z-input (right of the window) sees the mouth `[N2, Q]` of the z-pocket, through
the window and the sub-quadrilateral `WL, Q, N2, WR` of the room. -/
theorem al_zmouth_sees {A : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (alWL G) (alWR G) ⊆ A) (hRP : piece (alRoom G) ⊆ P.filled) {v : ℝ}
    (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) (hgA : inPt (G + 530) v ∈ A) :
    ∀ m ∈ segment (alN2 G) (alQ G), P.Sees (inPt (G + 530) v) m := by
  intro m hm
  set g := inPt (G + 530) v with hg
  have hg1 : g.1 = G + 530 := rfl
  have hg2 : g.2 = 4 * v - 2 := rfl
  set K := quad (alWL G) (alQ G) (alN2 G) (alWR G) with hK
  have hKR : piece K ⊆ piece (alRoom G) := by
    intro x hx
    obtain ⟨k1, k2, k3, k4⟩ := mem_piece_quad.1 hx
    simp only [det, alWL, alQ, alN2, alWR] at k1 k2 k3 k4
    exact mem_alRoom.2 ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hmK : m ∈ piece K := by
    have hc := convex_piece K
    have h1 : alN2 G ∈ piece K := by
      refine mem_piece_quad.2 ⟨?_, ?_, ?_, ?_⟩ <;> simp only [det, alWL, alQ, alN2, alWR] <;>
        linarith
    have h2 : alQ G ∈ piece K := by
      refine mem_piece_quad.2 ⟨?_, ?_, ?_, ?_⟩ <;> simp only [det, alWL, alQ, alN2, alWR] <;>
        linarith
    exact Geometry.segment_subset_of_convex hc h1 h2 hm
  obtain ⟨q, hq, hqm⟩ := cross_quad (a := alWL G) (b := alQ G) (c := alN2 G) (d := alWR G)
    (g := g) (by simp only [det, alN2, alWR, alWL]; linarith)
    (by simp only [det, alWR, alWL, alQ]; linarith)
    (by simp only [det, alWL, alQ]; rw [hg1, hg2]; nlinarith)
    (by simp only [det, alN2, alWR]; rw [hg1, hg2]; nlinarith)
    (by simp only [det, alWR, alWL]; rw [hg2]; nlinarith) hmK
  rw [Geometry.segment_comm] at hq
  exact sees_of_two_convex hA (convex_piece _) hAP hRP hgA (hKR hmK) (hWA hq) (alRoom_window hq)
    hqm

/-- The needles of `addLe` hanging from the room bottom (`y = −128`): the y-needle at `G + 210`
and the x-needle at `G + 370`. -/
noncomputable def alHungY (G H : ℝ) : Polygon := needleR (G + 210) (-128) H

/-- The x-needle of `addLe` (hanging from the room bottom at `G + 370`). -/
noncomputable def alHungX (G H : ℝ) : Polygon := needleR (G + 370) (-128) H

/-- The pieces of an `addLe` slot below the floor (except the floor needle of the z-input). -/
noncomputable def alPieces (G H : ℝ) : List Polygon :=
  [alRoom G, alPocketX G, alPocketY G, alPocketZ G, alAuxTri G, alHungY G H, alHungX G H]

/-- **`addLe` slot coverage (L7.8).**  `A` (the hall) is a convex part of the region containing
the window and the input guards; the pieces of the slot lie in the region; the walls of the
pockets are edges of `P`.  If `1/2 ≤ v_x, v_y`, `v_x + v_y ≤ v_z ≤ 2`, every point of every
piece is seen by the aux guard `alI G v_x v_y` or one of the input guards. -/
theorem al_slot_cover (hP : P.Simple) (hL : P.InteriorLeft) (hW : AlWalls P G) {A : Set Point}
    (hA : Convex ℝ A) (hAP : A ⊆ P.filled) (hWA : segment (alWL G) (alWR G) ⊆ A) {H : ℝ}
    (hH : 0 < H) (hKP : ∀ K ∈ alPieces G H, piece K ⊆ P.filled) {vx vy vz : ℝ}
    (hx1 : 1 / 2 ≤ vx) (hy1 : 1 / 2 ≤ vy) (hz2 : vz ≤ 2) (hrel : vx + vy ≤ vz)
    (hxA : inPt (G + 370) vx ∈ A) (hyA : inPt (G + 210) vy ∈ A) (hzA : inPt (G + 530) vz ∈ A) :
    ∀ K ∈ alPieces G H, ∀ z ∈ piece K, ∃ g ∈ ({alI G vx vy, inPt (G + 370) vx,
      inPt (G + 210) vy, inPt (G + 530) vz} : Set Point), P.Sees g z := by
  have hRP := hKP (alRoom G) (by simp [alPieces])
  have hXP := hKP (alPocketX G) (by simp [alPieces])
  have hYP := hKP (alPocketY G) (by simp [alPieces])
  have hZP := hKP (alPocketZ G) (by simp [alPieces])
  have hTP := hKP (alAuxTri G) (by simp [alPieces])
  have hNY := hKP (alHungY G H) (by simp [alPieces])
  have hNX := hKP (alHungX G H) (by simp [alPieces])
  have hxy : vx + vy ≤ 2 := by linarith
  have hx2 : vx ≤ 2 := by linarith
  have hy2 : vy ≤ 2 := by linarith
  have hz1 : 1 / 2 ≤ vz := by linarith
  have hI := alI_mem_auxRegion (G := G) hx1 hy1 hxy
  have hIf := alI_fst (G := G) (vx := vx) (vy := vy) hx2 (by linarith)
  obtain ⟨hcov1, hcov2, hcov3⟩ := al_cover_of_rel hA hAP hWA hRP hXP hYP hZP hx1 hy1 hz2 hxA hyA
    hzA hrel
  -- the aux guard sees the room
  have hauxR : ∀ z ∈ piece (alRoom G), P.Sees (alI G vx vy) z := fun z hz =>
    sees_of_convex (convex_piece _) hRP hI.2 hz
  -- the x- and y-inputs see the room
  have hxR : ∀ z ∈ piece (alRoom G), P.Sees (inPt (G + 370) vx) z :=
    al_room_sees hA hAP hWA hRP hxA (by simp only [inPt_fst]; linarith)
      (by simp only [inPt_fst, inPt_snd]; nlinarith) (by simp only [inPt_snd]; linarith)
  have hyR : ∀ z ∈ piece (alRoom G), P.Sees (inPt (G + 210) vy) z :=
    al_room_sees hA hAP hWA hRP hyA (by simp only [inPt_fst]; linarith)
      (by simp only [inPt_fst, inPt_snd]; nlinarith) (by simp only [inPt_snd]; linarith)
  have hleft : ∀ q : Point, q.1 = G + 50 → -128 ≤ q.2 → q.2 ≤ -445 / 4 →
      q ∈ piece (alRoom G) := fun q h1 h2 h3 => alRoom_left h1 h2 h3
  have hseg : ∀ {y₁ y₂ : ℝ}, y₁ ≤ y₂ → -128 ≤ y₁ → y₂ ≤ -445 / 4 →
      ∀ q ∈ segment ((G + 50, y₁) : Point) (G + 50, y₂), q ∈ piece (alRoom G) := by
    intro y₁ y₂ hy hy1 hy2 q hq
    obtain ⟨e1, e2, e3⟩ := (mem_segment_vert_iff hy).1 hq
    exact hleft q e1 (by linarith) (by linarith)
  have houtI : ∀ (lo dn up hi : Point), dn.1 = up.1 → dn.2 < up.2 → dn.1 = G + 50 →
      alI G vx vy ∉ piece (quad lo dn up hi) := fun lo dn up hi hd hdu h50 =>
    add_not_mem_pocket hd hdu (by rw [h50]; exact hIf)
  have houtIn : ∀ (lo dn up hi : Point) (g : Point), dn.1 = up.1 → dn.2 < up.2 →
      dn.1 = G + 50 → G + 50 < g.1 → g ∉ piece (quad lo dn up hi) :=
    fun lo dn up hi g hd hdu h50 hg => add_not_mem_pocket hd hdu (by rw [h50]; exact hg)
  intro K hK z hz
  simp only [alPieces, List.mem_cons, List.mem_nil_iff, or_false] at hK
  rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- room
    exact ⟨_, Or.inl rfl, hauxR z hz⟩
  · -- x-pocket
    obtain ⟨c1, c2, c3, c4⟩ := alPocketX_ccw (G := G)
    have := pocket_cover_of_sees hP hL c1 c2 c3 c4 hW.x0 hW.x2 hW.x3 hXP
      (Gs := {alI G vx vy, inPt (G + 370) vx})
      (fun g hg m hm => by
        have hmR := hseg (y₁ := -113) (y₂ := -445 / 4) (by norm_num) (by norm_num)
          (by norm_num) m (by simpa only [alP, alN1] using hm)
        rcases hg with rfl | rfl
        · exact hauxR m hmR
        · exact hxR m hmR)
      (fun g hg => by
        rcases hg with rfl | rfl
        · exact houtI _ _ _ _ (by simp [alP, alN1]) (by simp only [alP, alN1]; norm_num)
            (by simp [alP])
        · exact houtIn _ _ _ _ _ (by simp [alP, alN1]) (by simp only [alP, alN1]; norm_num)
            (by simp [alP]) (by simp only [inPt_fst]; linarith))
      (fun s hs => (hcov1 s hs).elim (fun h => ⟨_, Or.inl rfl, h⟩)
        (fun h => ⟨_, Or.inr rfl, h⟩)) z hz
    obtain ⟨g, hg, hgz⟩ := this
    rcases hg with rfl | rfl
    · exact ⟨_, Or.inl rfl, hgz⟩
    · exact ⟨_, Or.inr (Or.inl rfl), hgz⟩
  · -- y-pocket
    obtain ⟨c1, c2, c3, c4⟩ := alPocketY_ccw (G := G)
    have := pocket_cover_of_sees hP hL c1 c2 c3 c4 hW.y0 hW.y2 hW.y3 hYP
      (Gs := {alI G vx vy, inPt (G + 210) vy})
      (fun g hg m hm => by
        have hmR := hseg (y₁ := -128) (y₂ := -491 / 4) (by norm_num) (by norm_num)
          (by norm_num) m (by simpa only [alR, alN3] using hm)
        rcases hg with rfl | rfl
        · exact hauxR m hmR
        · exact hyR m hmR)
      (fun g hg => by
        rcases hg with rfl | rfl
        · exact houtI _ _ _ _ (by simp [alR, alN3]) (by simp only [alR, alN3]; norm_num)
            (by simp [alR])
        · exact houtIn _ _ _ _ _ (by simp [alR, alN3]) (by simp only [alR, alN3]; norm_num)
            (by simp [alR]) (by simp only [inPt_fst]; linarith))
      (fun s hs => (hcov2 s hs).elim (fun h => ⟨_, Or.inl rfl, h⟩)
        (fun h => ⟨_, Or.inr rfl, h⟩)) z hz
    obtain ⟨g, hg, hgz⟩ := this
    rcases hg with rfl | rfl
    · exact ⟨_, Or.inl rfl, hgz⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), hgz⟩
  · -- z-pocket
    obtain ⟨c1, c2, c3, c4⟩ := alPocketZ_ccw (G := G)
    have := pocket_cover_of_sees hP hL c1 c2 c3 c4 hW.z0 hW.z2 hW.z3 hZP
      (Gs := {alI G vx vy, inPt (G + 530) vz})
      (fun g hg m hm => by
        rcases hg with rfl | rfl
        · exact hauxR m (hseg (y₁ := -2994 / 25) (y₂ := -118) (by norm_num)
            (by norm_num) (by norm_num) m
            (by simpa only [alN2, alQ] using hm))
        · exact al_zmouth_sees hA hAP hWA hRP hz1 hz2 hzA m hm)
      (fun g hg => by
        rcases hg with rfl | rfl
        · exact houtI _ _ _ _ (by simp [alN2, alQ]) (by simp only [alN2, alQ]; norm_num)
            (by simp [alN2])
        · exact houtIn _ _ _ _ _ (by simp [alN2, alQ]) (by simp only [alN2, alQ]; norm_num)
            (by simp [alN2]) (by simp only [inPt_fst]; linarith))
      (fun s hs => (hcov3 s hs).elim (fun h => ⟨_, Or.inl rfl, h⟩)
        (fun h => ⟨_, Or.inr rfl, h⟩)) z hz
    obtain ⟨g, hg, hgz⟩ := this
    rcases hg with rfl | rfl
    · exact ⟨_, Or.inl rfl, hgz⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), hgz⟩
  · -- aux wedge
    obtain ⟨⟨k1, k2⟩, hk⟩ := hI
    have hk' := mem_alRoom.1 hk
    refine ⟨_, Or.inl rfl, wedge_sees (convex_piece _) hRP (a := alM1 G) (b := alTip G)
      (c := alM2 G) (by simp only [det, alM1, alTip, alM2]; norm_num) k1 k2
      (by simp only [det, alM2, alM1]; nlinarith) hk ?_ hTP z hz⟩
    intro q hq
    obtain ⟨e1, e2, e3⟩ := (mem_segment_horiz_iff (c := -128) (x₁ := G + 439 / 4)
      (x₂ := G + 441 / 4) (by linarith)).1
      (by rw [Geometry.segment_comm]; simpa only [alM1, alM2] using hq)
    exact mem_alRoom.2 ⟨by nlinarith, by linarith, by linarith, by linarith, by linarith⟩
  · -- y-needle
    refine ⟨_, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
    refine needleR_sees_via (s := G + 210) (y := 4 * vy - 2) hH (by linarith) (fun q hq => ?_)
      hNY z hz
    obtain ⟨e1, e2, e3⟩ := (mem_segment_horiz_iff (c := -128) (x₁ := G + 210)
      (x₂ := G + 210 + 1 / 4) (by linarith)).1 (by rw [Geometry.segment_comm]; exact hq)
    exact hyR q (mem_alRoom.2 ⟨by nlinarith, by linarith, by linarith, by linarith, by linarith⟩)
  · -- x-needle
    refine ⟨_, Or.inr (Or.inl rfl), ?_⟩
    refine needleR_sees_via (s := G + 370) (y := 4 * vx - 2) hH (by linarith) (fun q hq => ?_)
      hNX z hz
    obtain ⟨e1, e2, e3⟩ := (mem_segment_horiz_iff (c := -128) (x₁ := G + 370)
      (x₂ := G + 370 + 1 / 4) (by linarith)).1 (by rw [Geometry.segment_comm]; exact hq)
    exact hxR q (mem_alRoom.2 ⟨by nlinarith, by linarith, by linarith, by linarith, by linarith⟩)

end addLe

end ArtGallery.Stade

end
