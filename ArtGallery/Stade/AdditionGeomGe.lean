module

public import ArtGallery.Stade.AdditionGeom

/-!
# Stade construction, §7: geometry of the addition gadget `addGe`

Visibility facts for the gadget `addGe` (`v_z ≤ v_x + v_y`) of `docs/stade/construction.md` §7
(notation of `ArtGallery/Stade/AdditionAlg.lean`, slot origin `G`; generic tools in
`ArtGallery/Stade/AdditionGeom.lean`).  Compared with `addLe` all sides are reversed, and the
z-nook is reached through the **bay** `N1, N2, Q` (the triangle `agBay G`): the input opening
`N2 = (G + 65/2, −5977/100)` is recessed behind the room's left side `x = G + 50`, and the mouth of
the z-pocket is the slanted segment `[Q, N2]`.

* `ag_rel_of_cover` (L7.3, L7.4): coverage of the three nooks by the aux guard (any point right
  of `x = G + 50`) and the inputs implies `v_z ≤ v_x + v_y`;
* `ag_sees_auxTip`, `ag_aux_bounds`, `agI_mem_auxRegion`: the aux region `cone ∩ room` lies in
  `G + 80 ≤ x ≤ G + 84`, `y ≤ −1`, and contains the canonical aux point;
* `ag_viewer_x`, `ag_viewer_y`, `ag_viewer_z` (L7.6): viewers of the nooks outside the pockets
  lie, in the input band `0 ≤ y ≤ 6`, in `[G + 218, G + 421]`, `[G + 101, G + 221]`,
  `[G + 87, G + 148]` (the foreign inputs at `G + 185/2`, `G + 210`, `G + 370` are excluded with
  margins `8, 8.5, 62`);
* `ag_cover_of_rel`, `ag_cover_iff` (L7.7, L7.8 for the nooks): with the aux guard at the
  canonical point, the nooks are covered iff `v_z ≤ v_x + v_y`; the sight lines to the z-nook
  pass through the bay.
-/

@[expose] public section

namespace ArtGallery

namespace Stade

open ArtGallery.Geometry

variable {P : Polygon} {G : ℝ}

/-! ### Pockets and the bay -/

/-- `addGe`: the x-pocket `Xlo, N1, P, Xhi` (mouth `[N1, P]`). -/
noncomputable def agPocketX (G : ℝ) : Polygon := quad (agXlo G) (agN1 G) (agP G) (agXhi G)
/-- `addGe`: the y-pocket `Ylo, N3, R, Yhi` (mouth `[N3, R]`). -/
noncomputable def agPocketY (G : ℝ) : Polygon := quad (agYlo G) (agN3 G) (agR G) (agYhi G)
/-- `addGe`: the z-pocket `Zlo, Q, N2, Zhi` (slanted mouth `[Q, N2]`). -/
noncomputable def agPocketZ (G : ℝ) : Polygon := quad (agZlo G) (agQ G) (agN2 G) (agZhi G)
/-- `addGe`: the bay `N1, N2, Q` between the room and the z-pocket (wall `N1 → N2`, openings
`[N2, Q]` (the z-mouth) and `[Q, N1]` (on the room's left side)). -/
noncomputable def agBay (G : ℝ) : Polygon := tri (agN1 G) (agN2 G) (agQ G)

/-- The x-pocket of `addGe` is strictly convex and counter-clockwise. -/
theorem agPocketX_ccw :
    0 < det (agXlo G) (agN1 G) (agP G) ∧ 0 < det (agN1 G) (agP G) (agXhi G) ∧
      0 < det (agP G) (agXhi G) (agXlo G) ∧ 0 < det (agXhi G) (agXlo G) (agN1 G) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [det, agXlo, agN1, agP, agXhi] <;> linarith

/-- The y-pocket of `addGe` is strictly convex and counter-clockwise. -/
theorem agPocketY_ccw :
    0 < det (agYlo G) (agN3 G) (agR G) ∧ 0 < det (agN3 G) (agR G) (agYhi G) ∧
      0 < det (agR G) (agYhi G) (agYlo G) ∧ 0 < det (agYhi G) (agYlo G) (agN3 G) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [det, agYlo, agN3, agR, agYhi] <;> linarith

/-- The z-pocket of `addGe` is strictly convex and counter-clockwise. -/
theorem agPocketZ_ccw :
    0 < det (agZlo G) (agQ G) (agN2 G) ∧ 0 < det (agQ G) (agN2 G) (agZhi G) ∧
      0 < det (agN2 G) (agZhi G) (agZlo G) ∧ 0 < det (agZhi G) (agZlo G) (agQ G) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [det, agZlo, agQ, agN2, agZhi] <;> linarith

/-- The bay of `addGe` is a counter-clockwise triangle. -/
theorem agBay_ccw : 0 < det (agN1 G) (agN2 G) (agQ G) := by
  simp only [det, agN1, agN2, agQ]; linarith

/-- Points right of `x = G + 50` are not in the z-pocket of `addGe`. -/
theorem ag_not_mem_pocketZ {g : Point} (hg : G + 50 < g.1) : g ∉ piece (agPocketZ G) := by
  intro h
  obtain ⟨h0, h1, h2, h3⟩ := mem_piece_quad.1 h
  simp only [det, agZlo, agQ, agN2, agZhi] at h0 h1 h2 h3
  linarith

/-- The walls of the three pockets of `addGe` (`lo → dn`, `up → hi`, `hi → lo`) are edges of
`P`. -/
structure AgWalls (P : Polygon) (G : ℝ) : Prop where
  /-- x-pocket: `Xlo → N1`. -/
  x0 : PEdge P (agXlo G) (agN1 G)
  /-- x-pocket: `P → Xhi`. -/
  x2 : PEdge P (agP G) (agXhi G)
  /-- x-pocket: `Xhi → Xlo`. -/
  x3 : PEdge P (agXhi G) (agXlo G)
  /-- y-pocket: `Ylo → N3`. -/
  y0 : PEdge P (agYlo G) (agN3 G)
  /-- y-pocket: `R → Yhi`. -/
  y2 : PEdge P (agR G) (agYhi G)
  /-- y-pocket: `Yhi → Ylo`. -/
  y3 : PEdge P (agYhi G) (agYlo G)
  /-- z-pocket: `Zlo → Q`. -/
  z0 : PEdge P (agZlo G) (agQ G)
  /-- z-pocket: `N2 → Zhi`. -/
  z2 : PEdge P (agN2 G) (agZhi G)
  /-- z-pocket: `Zhi → Zlo`. -/
  z3 : PEdge P (agZhi G) (agZlo G)

/-- The x-nook segment of `addGe`, explicitly. -/
theorem ag_nookX_iff {s : Point} :
    s ∈ segment (agXlo G) (agXhi G) ↔ s.1 = G + 30 ∧ -2649 / 64 ≤ s.2 ∧ s.2 ≤ -2601 / 64 :=
  mem_segment_vert_iff (by norm_num)

/-- The y-nook segment of `addGe`, explicitly. -/
theorem ag_nookY_iff {s : Point} :
    s ∈ segment (agYlo G) (agYhi G) ↔ s.1 = G + 30 ∧ -855 / 8 ≤ s.2 ∧ s.2 ≤ -423 / 4 :=
  mem_segment_vert_iff (by norm_num)

/-- The z-nook segment of `addGe`, explicitly. -/
theorem ag_nookZ_iff {s : Point} :
    s ∈ segment (agZlo G) (agZhi G) ↔ s.1 = G + 30 ∧ -6001 / 96 ≤ s.2 ∧ s.2 ≤ -5941 / 96 :=
  mem_segment_vert_iff (by norm_num)

/-! ### What each guard sees (L7.3) -/

section Sees

variable (hP : P.Simple) (hL : P.InteriorLeft) (hW : AgWalls P G)
include hP hL hW

/-- `addGe`, x-nook: a guard `g` right of `x = G + 50` sees only heights `≥ π_{N1}(g)` and
`≤ π_P(g)`. -/
theorem ag_sees_x {g : Point} (hg : G + 50 < g.1) {h : ℝ}
    (hh : (G + 30, h) ∈ segment (agXlo G) (agXhi G)) (hs : P.Sees g (G + 30, h)) :
    vproj g (agN1 G) (G + 30) ≤ h ∧ h ≤ vproj g (agP G) (G + 30) := by
  obtain ⟨c1, c2, c3, c4⟩ := agPocketX_ccw (G := G)
  exact add_nook_bounds hP hL c1 c2 c3 c4 hW.x0 hW.x2 hW.x3
    (add_not_mem_pocket rfl (by simp only [agN1, agP]; norm_num) hg) hg hg hh hs

/-- `addGe`, y-nook: a guard `g` right of `x = G + 50` sees only heights `≥ π_{N3}(g)` and
`≤ π_R(g)`. -/
theorem ag_sees_y {g : Point} (hg : G + 50 < g.1) {h : ℝ}
    (hh : (G + 30, h) ∈ segment (agYlo G) (agYhi G)) (hs : P.Sees g (G + 30, h)) :
    vproj g (agN3 G) (G + 30) ≤ h ∧ h ≤ vproj g (agR G) (G + 30) := by
  obtain ⟨c1, c2, c3, c4⟩ := agPocketY_ccw (G := G)
  exact add_nook_bounds hP hL c1 c2 c3 c4 hW.y0 hW.y2 hW.y3
    (add_not_mem_pocket rfl (by simp only [agN3, agR]; norm_num) hg) hg hg hh hs

/-- `addGe`, z-nook: a guard `g` right of `x = G + 50` sees only heights `≥ π_Q(g)` and
`≤ π_{N2}(g)`. -/
theorem ag_sees_z {g : Point} (hg : G + 50 < g.1) {h : ℝ}
    (hh : (G + 30, h) ∈ segment (agZlo G) (agZhi G)) (hs : P.Sees g (G + 30, h)) :
    vproj g (agQ G) (G + 30) ≤ h ∧ h ≤ vproj g (agN2 G) (G + 30) := by
  obtain ⟨c1, c2, c3, c4⟩ := agPocketZ_ccw (G := G)
  have hg' : (agN2 G).1 < g.1 := by simp only [agN2]; linarith
  exact add_nook_bounds hP hL c1 c2 c3 c4 hW.z0 hW.z2 hW.z3 (ag_not_mem_pocketZ hg) hg hg' hh hs

end Sees

/-- The three nooks of `addGe` are covered by the aux guard `a` and the inputs of values
`v_x, v_y, v_z`. -/
def AgCover (P : Polygon) (G : ℝ) (a : Point) (vx vy vz : ℝ) : Prop :=
  (∀ s ∈ segment (agXlo G) (agXhi G), P.Sees a s ∨ P.Sees (inPt (G + 370) vx) s) ∧
    (∀ s ∈ segment (agYlo G) (agYhi G), P.Sees a s ∨ P.Sees (inPt (G + 210) vy) s) ∧
    (∀ s ∈ segment (agZlo G) (agZhi G), P.Sees a s ∨ P.Sees (inPt (G + 185 / 2) vz) s)

/-- **`addGe`: coverage ⇒ `v_z ≤ v_x + v_y` (L7.4).**  If the walls of the three pockets are
edges of `P` and the aux guard `a` (any point right of `x = G + 50`) and the three inputs cover
the three nook segments, then `v_z ≤ v_x + v_y`. -/
theorem ag_rel_of_cover (hP : P.Simple) (hL : P.InteriorLeft) (hW : AgWalls P G) {a : Point}
    (ha : G + 50 < a.1) {vx vy vz : ℝ} (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy)
    (hy2 : vy ≤ 2) (hz1 : 1 / 2 ≤ vz) (hz2 : vz ≤ 2) (hcov : AgCover P G a vx vy vz) :
    vz ≤ vx + vy := by
  obtain ⟨hcx, hcy, hcz⟩ := hcov
  refine ag_rel_of_cover_alg (G := G) a hx1 hx2 hy1 hy2 hz1 hz2 ?_ ?_ ?_
  · intro h h1 h2
    have hs : ((G + 30, h) : Point) ∈ segment (agXlo G) (agXhi G) := ag_nookX_iff.2 ⟨rfl, h1, h2⟩
    rcases hcx _ hs with hh | hh
    · exact Or.inl (ag_sees_x hP hL hW ha hs hh).2
    · right
      have := (ag_sees_x hP hL hW (by simp only [inPt_fst]; linarith) hs hh).1
      rwa [ag_shadow_x] at this
  · intro h h1 h2
    have hs : ((G + 30, h) : Point) ∈ segment (agYlo G) (agYhi G) := ag_nookY_iff.2 ⟨rfl, h1, h2⟩
    rcases hcy _ hs with hh | hh
    · exact Or.inl (ag_sees_y hP hL hW ha hs hh).2
    · right
      have := (ag_sees_y hP hL hW (by simp only [inPt_fst]; linarith) hs hh).1
      rwa [ag_shadow_y] at this
  · intro h h1 h2
    have hs : ((G + 30, h) : Point) ∈ segment (agZlo G) (agZhi G) := ag_nookZ_iff.2 ⟨rfl, h1, h2⟩
    rcases hcz _ hs with hh | hh
    · exact Or.inl (ag_sees_z hP hL hW ha hs hh).1
    · right
      have := (ag_sees_z hP hL hW (by simp only [inPt_fst]; linarith) hs hh).2
      rwa [ag_shadow_z] at this

/-! ### Partial visibility (L7.6) -/

section PV

variable (hP : P.Simple) (hL : P.InteriorLeft) (hW : AgWalls P G)
include hP hL hW

/-- **`addGe`, viewers of the x-nook.**  A point seeing a point of the x-nook is in the
x-pocket, or right of `x = G + 50`, and in the input band `0 ≤ y ≤ 6` in `[G + 218, G + 421]`
(so it is not on the inputs at `G + 185/2` and `G + 210`). -/
theorem ag_viewer_x {s p : Point} (hs : s ∈ segment (agXlo G) (agXhi G)) (hsees : P.Sees p s) :
    p ∈ piece (agPocketX G) ∨
      (G + 50 ≤ p.1 ∧ (p.2 ≤ 6 → p.1 ≤ G + 421) ∧ (0 ≤ p.2 → G + 218 ≤ p.1)) := by
  obtain ⟨c1, c2, c3, c4⟩ := agPocketX_ccw (G := G)
  rcases add_nook_viewer hP hL c1 c2 c3 c4 hW.x0 hW.x2 hW.x3 hs hsees with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · right
    simp only [det, agXlo, agN1, agP, agXhi] at h1 h2 h3
    exact ⟨by linarith, fun hy => by linarith, fun hy => by linarith⟩

/-- **`addGe`, viewers of the y-nook.**  A point seeing a point of the y-nook is in the
y-pocket, or right of `x = G + 50`, and in the input band in `[G + 101, G + 221]` (not on the
inputs at `G + 185/2`, `G + 370`). -/
theorem ag_viewer_y {s p : Point} (hs : s ∈ segment (agYlo G) (agYhi G)) (hsees : P.Sees p s) :
    p ∈ piece (agPocketY G) ∨
      (G + 50 ≤ p.1 ∧ (p.2 ≤ 6 → p.1 ≤ G + 221) ∧ (0 ≤ p.2 → G + 101 ≤ p.1)) := by
  obtain ⟨c1, c2, c3, c4⟩ := agPocketY_ccw (G := G)
  rcases add_nook_viewer hP hL c1 c2 c3 c4 hW.y0 hW.y2 hW.y3 hs hsees with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · right
    simp only [det, agYlo, agN3, agR, agYhi] at h1 h2 h3
    exact ⟨by linarith, fun hy => by linarith, fun hy => by linarith⟩

/-- **`addGe`, viewers of the z-nook.**  A point seeing a point of the z-nook is in the
z-pocket, or right of `x = G + 31`, and in the input band in `[G + 87, G + 148]` (not on the
inputs at `G + 210`, `G + 370`). -/
theorem ag_viewer_z {s p : Point} (hs : s ∈ segment (agZlo G) (agZhi G)) (hsees : P.Sees p s) :
    p ∈ piece (agPocketZ G) ∨
      (G + 31 ≤ p.1 ∧ (p.2 ≤ 6 → p.1 ≤ G + 148) ∧ (0 ≤ p.2 → G + 87 ≤ p.1)) := by
  obtain ⟨c1, c2, c3, c4⟩ := agPocketZ_ccw (G := G)
  rcases add_nook_viewer hP hL c1 c2 c3 c4 hW.z0 hW.z2 hW.z3 hs hsees with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · right
    simp only [det, agZlo, agQ, agN2, agZhi] at h1 h2 h3
    exact ⟨by linarith, fun hy => by linarith, fun hy => by linarith⟩

end PV

/-- The pockets and the bay of `addGe` lie in the strip `G + 30 ≤ x ≤ G + 50`, below the
floor. -/
theorem ag_pocket_bounds {p : Point}
    (hp : p ∈ piece (agPocketX G) ∨ p ∈ piece (agPocketY G) ∨ p ∈ piece (agPocketZ G) ∨
      p ∈ piece (agBay G)) :
    G + 30 ≤ p.1 ∧ p.1 ≤ G + 50 ∧ p.2 ≤ -37 := by
  rcases hp with hp | hp | hp | hp
  · obtain ⟨h0, h1, h2, h3⟩ := mem_piece_quad.1 hp
    simp only [det, agXlo, agN1, agP, agXhi] at h0 h1 h2 h3
    exact ⟨by linarith, by linarith, by linarith⟩
  · obtain ⟨h0, h1, h2, h3⟩ := mem_piece_quad.1 hp
    simp only [det, agYlo, agN3, agR, agYhi] at h0 h1 h2 h3
    exact ⟨by linarith, by linarith, by linarith⟩
  · obtain ⟨h0, h1, h2, h3⟩ := mem_piece_quad.1 hp
    simp only [det, agZlo, agQ, agN2, agZhi] at h0 h1 h2 h3
    exact ⟨by linarith, by linarith, by linarith⟩
  · obtain ⟨h0, h1, h2⟩ := mem_piece_tri.1 hp
    simp only [det, agN1, agN2, agQ] at h0 h1 h2
    exact ⟨by linarith, by linarith, by linarith⟩

/-! ### The room and the aux region -/

/-- `addGe`: tip of the aux wedge. -/
noncomputable def agTip (G : ℝ) : Point := (G + 82, -113)
/-- `addGe`: first mouth end of the aux wedge. -/
noncomputable def agM1 (G : ℝ) : Point := (G + 327 / 4, -94)
/-- `addGe`: second mouth end of the aux wedge. -/
noncomputable def agM2 (G : ℝ) : Point := (G + 329 / 4, -94)
/-- `addGe`: left end `WL` of the window. -/
noncomputable def agWL (G : ℝ) : Point := (G + 85, -1)
/-- `addGe`: right end `WR` of the window. -/
noncomputable def agWR (G : ℝ) : Point := (G + 363, -1)
/-- `addGe`: bottom right corner of the room. -/
noncomputable def agBR (G : ℝ) : Point := (G + 363, -94)

/-- `addGe`: the convex room `WL, T0 = P, B0 = N3, BR, WR` (walls `WL → T0`, `BR → WR`;
openings: the left side `x = G + 50`, the bottom `y = −94`, the window `y = −1`). -/
noncomputable def agRoom (G : ℝ) : Polygon := pent (agWL G) (agP G) (agN3 G) (agBR G) (agWR G)

/-- `addGe`: the aux wedge `M1, tip, M2`. -/
noncomputable def agAuxTri (G : ℝ) : Polygon := tri (agM1 G) (agTip G) (agM2 G)

/-- `addGe`: the cone of the aux wedge. -/
def agCone (G : ℝ) : Set Point := {p | 0 ≤ det (agM1 G) (agTip G) p ∧ 0 ≤ det (agTip G) (agM2 G) p}

/-- `addGe`: the **aux region** `cone ∩ room`. -/
def agAuxRegion (G : ℝ) : Set Point := agCone G ∩ piece (agRoom G)

/-- Membership in the room of `addGe`, in coordinates. -/
theorem mem_agRoom {p : Point} :
    p ∈ piece (agRoom G) ↔ 0 ≤ 36 * (p.1 - G - 50) - 35 * p.2 - 1295 ∧
      G + 50 ≤ p.1 ∧ -94 ≤ p.2 ∧ p.1 ≤ G + 363 ∧ p.2 ≤ -1 := by
  rw [agRoom, mem_piece_pent]
  simp only [det, agWL, agP, agN3, agBR, agWR]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The room of `addGe` is a convex piece. -/
theorem agRoom_isPiece : IsPiece (agRoom G) := by
  refine isPiece_pent ?_ (G + 200, -40) ?_
  · intro x hx
    rw [← agRoom, mem_agRoom]
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      simp only [agWL, agP, agN3, agBR, agWR] <;>
      exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · simp only [det, agWL, agP, agN3, agBR, agWR]
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Points of the left side `x = G + 50`, `−94 ≤ y ≤ −37` lie in the room. -/
theorem agRoom_left {q : Point} (h1 : q.1 = G + 50) (h2 : -94 ≤ q.2) (h3 : q.2 ≤ -37) :
    q ∈ piece (agRoom G) :=
  mem_agRoom.2 ⟨by rw [h1]; linarith, by linarith, h2, by linarith, by linarith⟩

/-- The window lies in the room. -/
theorem agRoom_window {q : Point} (hq : q ∈ segment (agWL G) (agWR G)) : q ∈ piece (agRoom G) := by
  obtain ⟨h1, h2, h3⟩ :=
    (mem_segment_horiz_iff (c := -1) (x₁ := G + 85) (x₂ := G + 363) (by linarith)).1 hq
  exact mem_agRoom.2 ⟨by rw [h1]; linarith, by linarith, by linarith, h3, by linarith⟩

/-- The walls of the aux wedge and of the room of `addGe` are edges of `P`. -/
structure AgAuxWalls (P : Polygon) (G : ℝ) : Prop where
  /-- Aux wedge: `M1 → tip`. -/
  w1 : PEdge P (agM1 G) (agTip G)
  /-- Aux wedge: `tip → M2`. -/
  w2 : PEdge P (agTip G) (agM2 G)
  /-- Room: `WL → T0`. -/
  r0 : PEdge P (agWL G) (agP G)
  /-- Room: `BR → WR`. -/
  r3 : PEdge P (agBR G) (agWR G)

/-- **`addGe`: viewers of the aux tip (L4.1').**  Every point seeing the tip of the aux wedge
lies in the aux wedge or in the aux region `cone ∩ room`. -/
theorem ag_sees_auxTip (hP : P.Simple) (hL : P.InteriorLeft) (hA : AgAuxWalls P G) {p : Point}
    (h : P.Sees p (agTip G)) : p ∈ piece (agAuxTri G) ∪ agAuxRegion G := by
  have htri : 0 < det (agM1 G) (agTip G) (agM2 G) := by
    simp only [det, agM1, agTip, agM2]; linarith
  have hWO : ∀ j < (agRoom G).n, (j = 1 ∨ j = 2 ∨ j = 4) ∨ IsWall P (agRoom G) j := by
    intro j hj
    simp only [agRoom, pent, Polygon.n, List.length_cons, List.length_nil] at hj
    interval_cases j
    · right; simpa [IsWall, PEdge, agRoom, pent, Polygon.vtx, Polygon.n] using hA.r0
    · left; left; rfl
    · left; right; left; rfl
    · right; simpa [IsWall, PEdge, agRoom, pent, Polygon.vtx, Polygon.n] using hA.r3
    · left; right; right; rfl
  have v2 : (agRoom G).vtx 2 = agN3 G := rfl
  have v3 : (agRoom G).vtx ((2 + 1) % (agRoom G).n) = agBR G := rfl
  have hj : 2 < (agRoom G).n := by simp [agRoom, pent, Polygon.n]
  have hm : ∀ q ∈ segment (agM2 G) (agM1 G), ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧
      q = lerp ((agRoom G).vtx 2) ((agRoom G).vtx ((2 + 1) % (agRoom G).n)) τ := by
    intro q hq
    obtain ⟨μ, hμ0, hμ1, rfl⟩ := mem_segment_iff_lerp.1 hq
    refine ⟨(129 / 4 - μ / 2) / 313, by linarith, by linarith, ?_⟩
    rw [v2, v3]
    ext
    · simp only [lerp_fst, agM1, agM2, agN3, agBR]; ring
    · simp only [lerp_snd, agM1, agM2, agN3, agBR]; ring
  have htip : det ((agRoom G).vtx 2) ((agRoom G).vtx ((2 + 1) % (agRoom G).n)) (agTip G) < 0 := by
    rw [v2, v3]; simp only [det, agN3, agBR, agTip]; linarith
  have hdoor : ∀ y ∈ door (agRoom G) (fun j => j = 1 ∨ j = 2 ∨ j = 4),
      0 < det ((agRoom G).vtx 2) ((agRoom G).vtx ((2 + 1) % (agRoom G).n)) y →
      0 ≤ det (agM1 G) (agTip G) y → 0 ≤ det (agTip G) (agM2 G) y → False := by
    rw [v2, v3]
    rintro y ⟨j, -, hO, hy⟩ hpos hc1 hc2
    simp only [det, agN3, agBR, agM1, agTip, agM2] at hpos hc1 hc2
    rcases hO with rfl | rfl | rfl
    · change y ∈ segment (agP G) (agN3 G) at hy
      obtain ⟨t, ht0, ht1, rfl⟩ := hy
      simp only [agP, agN3] at hc1
      nlinarith
    · change y ∈ segment (agN3 G) (agBR G) at hy
      obtain ⟨t, ht0, ht1, rfl⟩ := hy
      simp only [agN3, agBR] at hpos
      nlinarith
    · rw [show (agRoom G).edge 4 = segment (agWR G) (agWL G) from
        (pent_edge _ _ _ _ _).2.2.2.2] at hy
      obtain ⟨t, ht0, ht1, rfl⟩ := hy
      simp only [agWR, agWL] at hc2
      nlinarith
  rcases add_sees_wedge_room hP hL htri hA.w1 hA.w2 agRoom_isPiece hWO hj hm htip hdoor h with
    h' | ⟨h1, h2, h3⟩
  · exact Or.inl h'
  · exact Or.inr ⟨⟨h1, h2⟩, h3⟩

/-- **`addGe`: position of the aux viewers.**  The aux wedge and the aux region lie in
`G + 80 ≤ x ≤ G + 84`, `y ≤ −1` (right of `x = G + 50`, and away from the slabs `|x − b| ≤ 3` of
the inputs at `b = G + 185/2, G + 210, G + 370`). -/
theorem ag_aux_bounds {p : Point} (hp : p ∈ piece (agAuxTri G) ∪ agAuxRegion G) :
    G + 80 ≤ p.1 ∧ p.1 ≤ G + 84 ∧ p.2 ≤ -1 := by
  have key : ∀ q : Point, 0 ≤ det (agM1 G) (agTip G) q → 0 ≤ det (agTip G) (agM2 G) q →
      q.2 ≤ -1 → G + 80 ≤ q.1 ∧ q.1 ≤ G + 84 ∧ q.2 ≤ -1 := by
    intro q h1 h2 h3
    simp only [det, agM1, agTip, agM2] at h1 h2
    exact ⟨by linarith, by linarith, h3⟩
  rcases hp with hp | ⟨⟨h1, h2⟩, hR⟩
  · obtain ⟨h1, h2, h3⟩ := mem_piece_tri.1 hp
    refine key p h1 h2 ?_
    simp only [det, agM2, agM1] at h3
    linarith
  · exact key p h1 h2 (mem_agRoom.1 hR).2.2.2.2

/-- **`addGe`: the canonical aux point lies in the aux region** (for `(v_x, v_y) ∈ [1/2, 2]²`). -/
theorem agI_mem_auxRegion {vx vy : ℝ} (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy)
    (hy2 : vy ≤ 2) : agI G vx vy ∈ agAuxRegion G := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := agI_pos (G := G) hx1 hx2 hy1 hy2
  have hf := agI_fst (G := G) (vx := vx) (vy := vy) hx2 (by linarith)
  refine ⟨⟨?_, ?_⟩, mem_agRoom.2 ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith⟩⟩
  · simp only [det, agM1, agTip]; linarith
  · simp only [det, agTip, agM2]; linarith

/-! ### Positive visibility (L7.7, L7.8 for the nooks) -/

section Positive

variable {A : Set Point}

/-- `addGe`, x-nook: with the aux guard at `I(v_x, v_y)`, the aux guard and the x-input cover
the x-nook. -/
theorem ag_cover_x (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (agWL G) (agWR G) ⊆ A) (hRP : piece (agRoom G) ⊆ P.filled)
    (hXP : piece (agPocketX G) ⊆ P.filled) {vx vy : ℝ} (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2)
    (hy1 : 1 / 2 ≤ vy) (hy2 : vy ≤ 2) (hxA : inPt (G + 370) vx ∈ A) :
    ∀ s ∈ segment (agXlo G) (agXhi G), P.Sees (agI G vx vy) s ∨
      P.Sees (inPt (G + 370) vx) s := by
  intro s hs
  obtain ⟨hs1, hs2, hs3⟩ := ag_nookX_iff.1 hs
  have e : s = (G + 30, s.2) := Prod.ext hs1 rfl
  obtain ⟨c1, c2, c3, c4⟩ := agPocketX_ccw (G := G)
  have hsX : s ∈ piece (agPocketX G) := add_nook_subset c1 c2 c3 c4 hs
  have hmX : segment (agN1 G) (agP G) ⊆ piece (agPocketX G) := add_mouth_subset c1 c2 c3 c4
  have hy0 : (0 : ℝ) ≤ vy := by linarith
  have hmR : ∀ q ∈ segment (agN1 G) (agP G), q ∈ piece (agRoom G) := fun q hq => by
    obtain ⟨h1, h2, h3⟩ :=
      (mem_segment_vert_iff (c := G + 50) (y₁ := -153 / 4) (y₂ := -37) (by norm_num)).1 hq
    exact agRoom_left h1 (by linarith) h3
  have hd : ∀ p : Point, det (agN1 G) (agP G) p = -(5 / 4) * (p.1 - G - 50) := fun p => by
    simp only [det, agN1, agP]; ring
  rw [e]
  by_cases hh : s.2 ≤ agSx vx
  · left
    have hI := agI_mem_auxRegion (G := G) hx1 hx2 hy1 hy2
    have hIf := agI_fst (G := G) hx2 hy0
    obtain ⟨q, hq, hqs⟩ : ∃ q ∈ segment (agN1 G) (agP G),
        q ∈ segment (agI G vx vy) (G + 30, s.2) := by
      refine exists_cross_vert ?_ hIf hIf ?_
      · rw [hd, hd]; simp only; nlinarith
      · rw [agI_P hx2 hy0]
        have := agI_N1 (G := G) hx1 hx2 hy1 hy2
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    exact sees_of_two_convex (convex_piece _) (convex_piece _) hRP hXP hI.2 (e ▸ hsX) (hmR q hq)
      (hmX hq) hqs
  · right
    push Not at hh
    have hg1 : (agN1 G).1 < (inPt (G + 370) vx).1 := by simp only [agN1, inPt_fst]; linarith
    obtain ⟨q₂, hq₂, hq₂s⟩ : ∃ q ∈ segment (agN1 G) (agP G),
        q ∈ segment (inPt (G + 370) vx) (G + 30, s.2) := by
      refine exists_cross_vert ?_ hg1 hg1 ?_
      · rw [hd, hd]; simp only [inPt_fst]; nlinarith
      · rw [ag_shadow_x]
        have := ag_input_x_P (G := G) (v := vx) hx2
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    obtain ⟨q₁, hq₁, hq₁s⟩ : ∃ q ∈ segment ((G + 85, -1) : Point) (G + 363, -1),
        q ∈ segment (inPt (G + 370) vx) (G + 30, s.2) :=
      add_exists_cross_hline (by simp only [inPt_snd]; linarith) (by simp only; linarith)
        (by linarith) (by simp only [inPt_fst, inPt_snd]; nlinarith)
        (by simp only [inPt_fst, inPt_snd]; nlinarith)
    have hq₁2 : q₁.2 = -1 := ((mem_segment_horiz_iff (by linarith)).1 hq₁).1
    have hq₂2 : q₂.2 ≤ -37 :=
      ((mem_segment_vert_iff (c := G + 50) (y₁ := -153 / 4) (y₂ := -37) (by norm_num)).1 hq₂).2.2
    refine add_sees_chain3 hA hAP (convex_piece _) hRP (convex_piece _) hXP hxA (hWA hq₁)
      (agRoom_window hq₁) (hmR q₂ hq₂) (hmX hq₂) (e ▸ hsX) hq₁s ?_
    exact add_mem_segment_of_snd_le hq₁s hq₂s (by simp only [inPt_snd]; linarith)
      (by rw [hq₁2]; linarith)

/-- `addGe`, y-nook: with the aux guard at `I(v_x, v_y)`, the aux guard and the y-input cover
the y-nook. -/
theorem ag_cover_y (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (agWL G) (agWR G) ⊆ A) (hRP : piece (agRoom G) ⊆ P.filled)
    (hYP : piece (agPocketY G) ⊆ P.filled) {vx vy : ℝ} (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2)
    (hy1 : 1 / 2 ≤ vy) (hy2 : vy ≤ 2) (hyA : inPt (G + 210) vy ∈ A) :
    ∀ s ∈ segment (agYlo G) (agYhi G), P.Sees (agI G vx vy) s ∨
      P.Sees (inPt (G + 210) vy) s := by
  intro s hs
  obtain ⟨hs1, hs2, hs3⟩ := ag_nookY_iff.1 hs
  have e : s = (G + 30, s.2) := Prod.ext hs1 rfl
  obtain ⟨c1, c2, c3, c4⟩ := agPocketY_ccw (G := G)
  have hsY : s ∈ piece (agPocketY G) := add_nook_subset c1 c2 c3 c4 hs
  have hmY : segment (agN3 G) (agR G) ⊆ piece (agPocketY G) := add_mouth_subset c1 c2 c3 c4
  have hy0 : (0 : ℝ) ≤ vy := by linarith
  have hmR : ∀ q ∈ segment (agN3 G) (agR G), q ∈ piece (agRoom G) := fun q hq => by
    obtain ⟨h1, h2, h3⟩ :=
      (mem_segment_vert_iff (c := G + 50) (y₁ := -94) (y₂ := -77) (by norm_num)).1 hq
    exact agRoom_left h1 h2 (by linarith)
  have hd : ∀ p : Point, det (agN3 G) (agR G) p = -17 * (p.1 - G - 50) := fun p => by
    simp only [det, agN3, agR]; ring
  rw [e]
  by_cases hh : s.2 ≤ agSy vy
  · left
    have hI := agI_mem_auxRegion (G := G) hx1 hx2 hy1 hy2
    have hIf := agI_fst (G := G) hx2 hy0
    obtain ⟨q, hq, hqs⟩ : ∃ q ∈ segment (agN3 G) (agR G),
        q ∈ segment (agI G vx vy) (G + 30, s.2) := by
      refine exists_cross_vert ?_ hIf hIf ?_
      · rw [hd, hd]; simp only; nlinarith
      · rw [agI_R hx2 hy0]
        have := agI_N3 (G := G) hx1 hx2 hy1 hy2
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    exact sees_of_two_convex (convex_piece _) (convex_piece _) hRP hYP hI.2 (e ▸ hsY) (hmR q hq)
      (hmY hq) hqs
  · right
    push Not at hh
    have hg1 : (agN3 G).1 < (inPt (G + 210) vy).1 := by simp only [agN3, inPt_fst]; linarith
    obtain ⟨q₂, hq₂, hq₂s⟩ : ∃ q ∈ segment (agN3 G) (agR G),
        q ∈ segment (inPt (G + 210) vy) (G + 30, s.2) := by
      refine exists_cross_vert ?_ hg1 hg1 ?_
      · rw [hd, hd]; simp only [inPt_fst]; nlinarith
      · rw [ag_shadow_y]
        have := ag_input_y_R (G := G) (v := vy) hy2
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    obtain ⟨q₁, hq₁, hq₁s⟩ : ∃ q ∈ segment ((G + 85, -1) : Point) (G + 363, -1),
        q ∈ segment (inPt (G + 210) vy) (G + 30, s.2) :=
      add_exists_cross_hline (by simp only [inPt_snd]; linarith) (by simp only; linarith)
        (by linarith) (by simp only [inPt_fst, inPt_snd]; nlinarith)
        (by simp only [inPt_fst, inPt_snd]; nlinarith)
    have hq₁2 : q₁.2 = -1 := ((mem_segment_horiz_iff (by linarith)).1 hq₁).1
    have hq₂2 : q₂.2 ≤ -77 :=
      ((mem_segment_vert_iff (c := G + 50) (y₁ := -94) (y₂ := -77) (by norm_num)).1 hq₂).2.2
    refine add_sees_chain3 hA hAP (convex_piece _) hRP (convex_piece _) hYP hyA (hWA hq₁)
      (agRoom_window hq₁) (hmR q₂ hq₂) (hmY hq₂) (e ▸ hsY) hq₁s ?_
    exact add_mem_segment_of_snd_le hq₁s hq₂s (by simp only [inPt_snd]; linarith)
      (by rw [hq₁2]; linarith)

/-- `addGe`, z-nook (through the bay, L7.7): with the aux guard at `I(v_x, v_y)` and
`v_z ≤ v_x + v_y`, the aux guard and the z-input cover the z-nook; their sight lines cross the
room's left side between `Q` and `N1` into the bay, then the mouth `[Q, N2]`. -/
theorem ag_cover_z (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (agWL G) (agWR G) ⊆ A) (hRP : piece (agRoom G) ⊆ P.filled)
    (hBP : piece (agBay G) ⊆ P.filled) (hZP : piece (agPocketZ G) ⊆ P.filled) {vx vy vz : ℝ}
    (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy) (hy2 : vy ≤ 2) (hz1 : 1 / 2 ≤ vz)
    (hz2 : vz ≤ 2) (hzA : inPt (G + 185 / 2) vz ∈ A) (hrel : vz ≤ vx + vy) :
    ∀ s ∈ segment (agZlo G) (agZhi G), P.Sees (agI G vx vy) s ∨
      P.Sees (inPt (G + 185 / 2) vz) s := by
  intro s hs
  obtain ⟨hs1, hs2, hs3⟩ := ag_nookZ_iff.1 hs
  have e : s = (G + 30, s.2) := Prod.ext hs1 rfl
  obtain ⟨c1, c2, c3, c4⟩ := agPocketZ_ccw (G := G)
  have hsZ : s ∈ piece (agPocketZ G) := add_nook_subset c1 c2 c3 c4 hs
  have hmZ : segment (agQ G) (agN2 G) ⊆ piece (agPocketZ G) := add_mouth_subset c1 c2 c3 c4
  have hBay := isPiece_tri (agBay_ccw (G := G))
  have hmB : segment (agQ G) (agN2 G) ⊆ piece (agBay G) := fun q hq => by
    rw [segment_comm] at hq
    exact edge_subset_piece hBay (j := 1) (by simp [tri, Polygon.n])
      (by simpa [Polygon.edge, agBay, tri, Polygon.vtx, Polygon.n] using hq)
  have hbB : segment (agQ G) (agN1 G) ⊆ piece (agBay G) := fun q hq =>
    edge_subset_piece hBay (j := 2) (by simp [tri, Polygon.n])
      (by simpa [Polygon.edge, agBay, tri, Polygon.vtx, Polygon.n] using hq)
  have hy0 : (0 : ℝ) ≤ vy := by linarith
  have hbR : ∀ q ∈ segment (agQ G) (agN1 G), q ∈ piece (agRoom G) := fun q hq => by
    obtain ⟨h1, h2, h3⟩ :=
      (mem_segment_vert_iff (c := G + 50) (y₁ := -151 / 3) (y₂ := -153 / 4) (by norm_num)).1 hq
    exact agRoom_left h1 (by linarith) (by linarith)
  have hb2 : ∀ q ∈ segment (agQ G) (agN1 G), -151 / 3 ≤ q.2 := fun q hq =>
    ((mem_segment_vert_iff (c := G + 50) (y₁ := -151 / 3) (y₂ := -153 / 4)
      (by norm_num)).1 hq).2.1
  have hb1 : ∀ q ∈ segment (agQ G) (agN1 G), q.1 = G + 50 := fun q hq =>
    ((mem_segment_vert_iff (c := G + 50) (y₁ := -151 / 3) (y₂ := -153 / 4)
      (by norm_num)).1 hq).1
  have hm1 : ∀ q ∈ segment (agQ G) (agN2 G), q.1 ≤ G + 50 := fun q hq => by
    obtain ⟨t, ht0, ht1, rfl⟩ := hq
    simp only [agQ, agN2]; nlinarith
  have hdb : ∀ p : Point, det (agQ G) (agN1 G) p = -(145 / 12) * (p.1 - G - 50) := fun p => by
    simp only [det, agQ, agN1]; ring
  have hdm : ∀ p : Point, det (agQ G) (agN2 G) p =
      2831 / 300 * (p.1 - G - 50) - 35 / 2 * p.2 - 5285 / 6 := fun p => by
    simp only [det, agQ, agN2]; ring
  have hds : 0 < det (agQ G) (agN2 G) (G + 30, s.2) := by rw [hdm]; simp only; linarith
  rw [e]
  by_cases hh : vproj (agI G vx vy) (agQ G) (G + 30) ≤ s.2
  · left
    have hI := agI_mem_auxRegion (G := G) hx1 hx2 hy1 hy2
    have hIf := agI_fst (G := G) hx2 hy0
    have hIpos := (agI_pos (G := G) hx1 hx2 hy1 hy2).2.2.2.2.2.2
    obtain ⟨q₂, hq₂, hq₂s⟩ : ∃ q ∈ segment (agQ G) (agN1 G),
        q ∈ segment (agI G vx vy) (G + 30, s.2) := by
      refine exists_cross_vert ?_ hIf hIf ?_
      · rw [hdb, hdb]; simp only; nlinarith
      · have := agI_N1_z (G := G) hx1 hx2 hy1 hy2
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have hN2 : (agN2 G).1 < (agI G vx vy).1 := by simp only [agN2]; linarith
    obtain ⟨q₃, hq₃, hq₃s⟩ : ∃ q ∈ segment (agQ G) (agN2 G),
        q ∈ segment (agI G vx vy) (G + 30, s.2) := by
      refine exists_cross_vert ?_ hIf hN2 ?_
      · have : det (agQ G) (agN2 G) (agI G vx vy) < 0 := by rw [hdm]; linarith
        nlinarith
      · have := agI_N2 (G := G) hx1 hx2 hy1 hy2
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    refine add_sees_chain3 (convex_piece _) hRP (convex_piece _) hBP (convex_piece _) hZP hI.2
      (hbR q₂ hq₂) (hbB hq₂) (hmB hq₃) (hmZ hq₃) (e ▸ hsZ) hq₂s ?_
    exact add_mem_segment_of_fst_le hq₂s hq₃s (by simp only; linarith)
      (by rw [hb1 q₂ hq₂]; exact hm1 q₃ hq₃)
  · right
    push Not at hh
    have hzs : s.2 ≤ agSz vz := le_trans hh.le ((agI_Q_le_iff hx2 hy0).2 hrel)
    have hg1 : (agQ G).1 < (inPt (G + 185 / 2) vz).1 := by simp only [agQ, inPt_fst]; linarith
    have hgN2 : (agN2 G).1 < (inPt (G + 185 / 2) vz).1 := by
      simp only [agN2, inPt_fst]; linarith
    obtain ⟨q₂, hq₂, hq₂s⟩ : ∃ q ∈ segment (agQ G) (agN1 G),
        q ∈ segment (inPt (G + 185 / 2) vz) (G + 30, s.2) := by
      refine exists_cross_vert ?_ hg1 hg1 ?_
      · rw [hdb, hdb]; simp only [inPt_fst]; nlinarith
      · have h1 := ag_input_z_Q (G := G) (v := vz) (by linarith)
        have h2 := ag_input_z_N1 (G := G) (v := vz) hz2
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    obtain ⟨q₃, hq₃, hq₃s⟩ : ∃ q ∈ segment (agQ G) (agN2 G),
        q ∈ segment (inPt (G + 185 / 2) vz) (G + 30, s.2) := by
      refine exists_cross_vert ?_ hg1 hgN2 ?_
      · have : det (agQ G) (agN2 G) (inPt (G + 185 / 2) vz) < 0 := by
          rw [hdm]; simp only [inPt_fst, inPt_snd]; linarith
        nlinarith
      · rw [ag_shadow_z]
        have := ag_input_z_Q (G := G) (v := vz) (by linarith)
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    obtain ⟨q₁, hq₁, hq₁s⟩ : ∃ q ∈ segment ((G + 85, -1) : Point) (G + 363, -1),
        q ∈ segment (inPt (G + 185 / 2) vz) (G + 30, s.2) :=
      add_exists_cross_hline (by simp only [inPt_snd]; linarith) (by simp only; linarith)
        (by linarith) (by simp only [inPt_fst, inPt_snd]; nlinarith)
        (by simp only [inPt_fst, inPt_snd]; nlinarith)
    have hq₁2 : q₁.2 = -1 := ((mem_segment_horiz_iff (by linarith)).1 hq₁).1
    have hq₂2 : q₂.2 ≤ -153 / 4 :=
      ((mem_segment_vert_iff (c := G + 50) (y₁ := -151 / 3) (y₂ := -153 / 4)
        (by norm_num)).1 hq₂).2.2
    refine add_sees_chain4 hA hAP (convex_piece _) hRP (convex_piece _) hBP (convex_piece _) hZP
      hzA (hWA hq₁) (agRoom_window hq₁) (hbR q₂ hq₂) (hbB hq₂) (hmB hq₃) (hmZ hq₃) (e ▸ hsZ)
      hq₁s ?_ ?_
    · exact add_mem_segment_of_snd_le hq₁s hq₂s (by simp only [inPt_snd]; linarith)
        (by rw [hq₁2]; linarith)
    · exact add_mem_segment_of_fst_le hq₂s hq₃s (by simp only [inPt_fst]; linarith)
        (by rw [hb1 q₂ hq₂]; exact hm1 q₃ hq₃)

/-- **`addGe`: `v_z ≤ v_x + v_y` ⇒ coverage (L7.8 for the nooks).**  Let `A` (the hall) be a
convex part of the region containing the window and the three inputs, and let the room, the
bay and the three pockets lie in the region.  With the aux guard at the canonical point
`I(v_x, v_y)`, the three nooks are covered. -/
theorem ag_cover_of_rel (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (agWL G) (agWR G) ⊆ A) (hRP : piece (agRoom G) ⊆ P.filled)
    (hBP : piece (agBay G) ⊆ P.filled) (hXP : piece (agPocketX G) ⊆ P.filled)
    (hYP : piece (agPocketY G) ⊆ P.filled) (hZP : piece (agPocketZ G) ⊆ P.filled)
    {vx vy vz : ℝ} (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy) (hy2 : vy ≤ 2)
    (hz1 : 1 / 2 ≤ vz) (hz2 : vz ≤ 2) (hxA : inPt (G + 370) vx ∈ A)
    (hyA : inPt (G + 210) vy ∈ A) (hzA : inPt (G + 185 / 2) vz ∈ A) (hrel : vz ≤ vx + vy) :
    AgCover P G (agI G vx vy) vx vy vz :=
  ⟨ag_cover_x hA hAP hWA hRP hXP hx1 hx2 hy1 hy2 hxA,
    ag_cover_y hA hAP hWA hRP hYP hx1 hx2 hy1 hy2 hyA,
    ag_cover_z hA hAP hWA hRP hBP hZP hx1 hx2 hy1 hy2 hz1 hz2 hzA hrel⟩

/-- **`addGe`: the three nooks are covered iff `v_z ≤ v_x + v_y`** (aux guard at the canonical
point `I(v_x, v_y)`, all values in `[1/2, 2]`). -/
theorem ag_cover_iff (hP : P.Simple) (hL : P.InteriorLeft) (hW : AgWalls P G)
    (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (agWL G) (agWR G) ⊆ A) (hRP : piece (agRoom G) ⊆ P.filled)
    (hBP : piece (agBay G) ⊆ P.filled) (hXP : piece (agPocketX G) ⊆ P.filled)
    (hYP : piece (agPocketY G) ⊆ P.filled) (hZP : piece (agPocketZ G) ⊆ P.filled)
    {vx vy vz : ℝ} (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy) (hy2 : vy ≤ 2)
    (hz1 : 1 / 2 ≤ vz) (hz2 : vz ≤ 2) (hxA : inPt (G + 370) vx ∈ A)
    (hyA : inPt (G + 210) vy ∈ A) (hzA : inPt (G + 185 / 2) vz ∈ A) :
    AgCover P G (agI G vx vy) vx vy vz ↔ vz ≤ vx + vy :=
  ⟨ag_rel_of_cover hP hL hW (agI_fst hx2 (by linarith)) hx1 hx2 hy1 hy2 hz1 hz2,
    ag_cover_of_rel hA hAP hWA hRP hBP hXP hYP hZP hx1 hx2 hy1 hy2 hz1 hz2 hxA hyA hzA⟩

end Positive

/-! ### The template chain -/

/-- The `addGe` gadget chain of `Templates.lean`, translated by `ox` (needle tips at depth `H`),
is `WL, P, Xhi, Xlo, N1, N2, Zhi, Zlo, Q, R, Yhi, Ylo, N3, M1, tip, M2`, the needles of the
z- and y-inputs hanging from the bottom, `BR, WR`. -/
theorem chainAddGe_inst (H ox : ℚ) :
    chainAddGe.map (fun p => ratPoint (p.inst H ox)) =
      [agWL (ox : ℝ), agP (ox : ℝ), agXhi (ox : ℝ), agXlo (ox : ℝ), agN1 (ox : ℝ), agN2 (ox : ℝ),
        agZhi (ox : ℝ), agZlo (ox : ℝ), agQ (ox : ℝ), agR (ox : ℝ), agYhi (ox : ℝ),
        agYlo (ox : ℝ), agN3 (ox : ℝ), agM1 (ox : ℝ), agTip (ox : ℝ), agM2 (ox : ℝ),
        ((ox : ℝ) + 185 / 2, -94), ((ox : ℝ) + 185 / 2, -94 - (H : ℝ)),
        ((ox : ℝ) + 371 / 4, -94), ((ox : ℝ) + 210, -94), ((ox : ℝ) + 210, -94 - (H : ℝ)),
        ((ox : ℝ) + 841 / 4, -94), agBR (ox : ℝ), agWR (ox : ℝ)] := by
  simp only [chainAddGe, List.map_cons, List.map_nil, Chain.RPt.inst, ratPoint, agWL, agP,
    agXhi, agXlo, agN1, agN2, agZhi, agZlo, agQ, agR, agYhi, agYlo, agN3, agM1, agTip, agM2, agBR,
    agWR]
  push_cast
  norm_num

end Stade

end ArtGallery

end
