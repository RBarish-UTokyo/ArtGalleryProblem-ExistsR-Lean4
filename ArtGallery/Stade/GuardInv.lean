module

public import ArtGallery.Stade.GuardWedges
public import ArtGallery.Stade.Inversion

/-!
# The canonical guards see the inversion gadgets (proof plan L6.5)

For a slot with origin `G` holding an inversion gadget, with input guards `inPt (G + δ) v` at the
values of the variables:

* `invGe`: each input guard sees the whole corridor `C1 P Q C2` (through the floor opening
  `[C1, C2]`, `cross_quad`), hence the mouth `[P, Q]`; if `1 ≤ v_x v_y`, every nook point is
  reached through the mouth by one of them, so they see the whole pocket (`pocket_cover`) —
  `ig_corridor_sees`, `ig_pocket_cover`;
* `invRevLe`: the same with the corridor triangle `P Q Q'` (`ir_corridor_sees`,
  `ir_pocket_cover`); moreover the x-guard sees the needle hanging from the pocket wall `I Q`
  (`ir_needle_sees`) through the mouth and the sub-quadrilateral `P, m₁, m₂, Q` of the pocket.
-/

@[expose] public section

namespace ArtGallery.Stade

variable {P : Polygon} {G : ℝ}

/-! ### `invGe` -/

/-- An input guard of `invGe` sees the whole corridor. -/
theorem ig_corridor_sees {A : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hfA : segment (igC1 G) (igC2 G) ⊆ A) (hBP : piece (igCorridor G) ⊆ P.filled) {g : Point}
    (hgA : g ∈ A) (hx1 : G + 40 ≤ g.1) (hx2 : g.1 ≤ G + 100) (hy1 : 0 ≤ g.2) (hy2 : g.2 ≤ 6) :
    ∀ z ∈ piece (igCorridor G), P.Sees g z := by
  intro z hz
  obtain ⟨q, hq, hqz⟩ := cross_quad (a := igC1 G) (b := igP G) (c := igQ G) (d := igC2 G) (g := g)
    (by unfold det igQ igC2 igC1; norm_num) (by unfold det igC2 igC1 igP; norm_num)
    (by unfold det igC1 igP; simp only; nlinarith) (by unfold det igQ igC2; simp only; nlinarith)
    (by unfold det igC2 igC1; simp only; nlinarith) hz
  rw [Geometry.segment_comm] at hq
  exact sees_of_two_convex hA (convex_piece _) hAP hBP hgA hz (hfA hq)
    (ig_floor_subset_corridor hq) hqz

/-- **`invGe` pocket coverage**: if `1 ≤ v w`, the two input guards see every point of the
pocket. -/
theorem ig_pocket_cover {A : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hfA : segment (igC1 G) (igC2 G) ⊆ A) (hBP : piece (igCorridor G) ⊆ P.filled)
    (hCP : piece (igPocket G) ⊆ P.filled) {v w : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2) (hxA : inPt (G + 40) v ∈ A) (hyA : inPt (G + 100) w ∈ A)
    (hrel : 1 ≤ v * w) :
    ∀ z ∈ piece (igPocket G), P.Sees (inPt (G + 40) v) z ∨ P.Sees (inPt (G + 100) w) z := by
  obtain ⟨h1, h2, h3, h4⟩ := ig_pocket_ccw (G := G)
  have hmouth : ∀ g ∈ ({inPt (G + 40) v, inPt (G + 100) w} : Set Point),
      ∀ m ∈ segment (igQ G) (igP G), P.Sees g m := by
    intro g hg m hm
    rw [Geometry.segment_comm] at hm
    have hmB := ig_mouth_subset_corridor hm
    rcases hg with rfl | rfl
    · exact ig_corridor_sees hA hAP hfA hBP hxA (by simp only [inPt_fst, inPt_snd]; linarith)
        (by simp only [inPt_fst, inPt_snd]; linarith) (by simp only [inPt_fst, inPt_snd]; linarith)
        (by simp only [inPt_fst, inPt_snd]; linarith) m hmB
    · exact ig_corridor_sees hA hAP hfA hBP hyA (by simp only [inPt_fst, inPt_snd]; linarith)
        (by simp only [inPt_fst, inPt_snd]; linarith) (by simp only [inPt_fst, inPt_snd]; linarith)
        (by simp only [inPt_fst, inPt_snd]; linarith) m hmB
  have hcov := pocket_cover (P := P) h1 h2 h3 h4 hCP hmouth (fun s hs => by
    rw [Geometry.segment_comm] at hs
    obtain ⟨e1, e2, e3⟩ := ig_nook_iff.1 hs
    have e : s = (s.1, -78) := Prod.ext rfl e1
    by_cases hsh : igShX G v ≤ s.1
    · obtain ⟨q, hq, hqs⟩ := ig_x_cross (g := G) hv1 hsh e3
      rw [Geometry.segment_comm] at hq
      exact ⟨_, Or.inl rfl, q, hq, by rw [e]; exact hqs⟩
    · push Not at hsh
      have hle := (igSh_le_iff (g := G) (by linarith) (by linarith)).2 hrel
      obtain ⟨q, hq, hqs⟩ := ig_y_cross (g := G) hw1 e2 (by linarith)
      rw [Geometry.segment_comm] at hq
      exact ⟨_, Or.inr rfl, q, hq, by rw [e]; exact hqs⟩)
  intro z hz
  obtain ⟨g, hg, hgz⟩ := hcov z hz
  rcases hg with rfl | rfl
  · exact Or.inl hgz
  · exact Or.inr hgz

/-! ### `invRevLe` -/

/-- An input guard of `invRevLe` sees the whole corridor triangle. -/
theorem ir_corridor_sees {A : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hfA : segment (irP G) (irQ' G) ⊆ A) (hBP : piece (irCorridor G) ⊆ P.filled) {g : Point}
    (hgA : g ∈ A) (hx1 : G + 59 ≤ g.1) (hx2 : g.1 ≤ G + 104) (hy1 : 0 ≤ g.2) :
    ∀ z ∈ piece (irCorridor G), P.Sees g z := by
  intro z hz
  obtain ⟨q, hq, hqz⟩ := cross_tri (a := irP G) (b := irQ G) (c := irQ' G) (g := g)
    (by unfold det irP irQ irQ'; norm_num) (by unfold det irP irQ; simp only; nlinarith)
    (by unfold det irQ irQ'; simp only; nlinarith) (by unfold det irQ' irP; simp only; nlinarith)
    hz
  rw [Geometry.segment_comm] at hq
  exact sees_of_two_convex hA (convex_piece _) hAP hBP hgA hz (hfA hq)
    (ir_floor_subset_corridor hq) hqz

/-- The x-guard of `invRevLe` sees the corridor. -/
theorem ir_corridor_sees_x {A : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hfA : segment (irP G) (irQ' G) ⊆ A) (hBP : piece (irCorridor G) ⊆ P.filled) {v : ℝ}
    (hv1 : 1 / 2 ≤ v) (hxA : inPt (G + 60) v ∈ A) :
    ∀ z ∈ piece (irCorridor G), P.Sees (inPt (G + 60) v) z :=
  ir_corridor_sees hA hAP hfA hBP hxA (by simp only [inPt_fst, inPt_snd]; linarith)
    (by simp only [inPt_fst, inPt_snd]; linarith) (by simp only [inPt_fst, inPt_snd]; linarith)

/-- The y-guard of `invRevLe` sees the corridor. -/
theorem ir_corridor_sees_y {A : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hfA : segment (irP G) (irQ' G) ⊆ A) (hBP : piece (irCorridor G) ⊆ P.filled) {w : ℝ}
    (hw1 : 1 / 2 ≤ w) (hyA : inPt (G + 104) w ∈ A) :
    ∀ z ∈ piece (irCorridor G), P.Sees (inPt (G + 104) w) z :=
  ir_corridor_sees hA hAP hfA hBP hyA (by simp only [inPt_fst, inPt_snd]; linarith)
    (by simp only [inPt_fst, inPt_snd]; linarith) (by simp only [inPt_fst, inPt_snd]; linarith)

/-- **`invRevLe` pocket coverage**: if `v (5/2 − w) ≤ 1`, the two input guards see every point
of the pocket. -/
theorem ir_pocket_cover {A : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hfA : segment (irP G) (irQ' G) ⊆ A) (hBP : piece (irCorridor G) ⊆ P.filled)
    (hCP : piece (irPocket G) ⊆ P.filled) {v w : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2) (hxA : inPt (G + 60) v ∈ A) (hyA : inPt (G + 104) w ∈ A)
    (hrel : v * (5 / 2 - w) ≤ 1) :
    ∀ z ∈ piece (irPocket G), P.Sees (inPt (G + 60) v) z ∨ P.Sees (inPt (G + 104) w) z := by
  obtain ⟨h1, h2, h3, h4⟩ := ir_pocket_ccw (G := G)
  have hmouth : ∀ g ∈ ({inPt (G + 60) v, inPt (G + 104) w} : Set Point),
      ∀ m ∈ segment (irQ G) (irP G), P.Sees g m := by
    intro g hg m hm
    rw [Geometry.segment_comm] at hm
    have hmB := ir_mouth_subset_corridor hm
    rcases hg with rfl | rfl
    · exact ir_corridor_sees_x hA hAP hfA hBP hv1 hxA m hmB
    · exact ir_corridor_sees_y hA hAP hfA hBP hw1 hyA m hmB
  have hcov := pocket_cover (P := P) h1 h2 h3 h4 hCP hmouth (fun s hs => by
    rw [Geometry.segment_comm] at hs
    obtain ⟨e1, e2, e3⟩ := ir_nook_iff.1 hs
    have e : s = (s.1, -22) := Prod.ext rfl e1
    by_cases hsh : irShX G v ≤ s.1
    · obtain ⟨q, hq, hqs⟩ := ir_x_cross (g := G) hv1 hsh e3
      rw [Geometry.segment_comm] at hq
      exact ⟨_, Or.inl rfl, q, hq, by rw [e]; exact hqs⟩
    · push Not at hsh
      have hle := (irSh_le_iff (g := G) hv1 (by linarith)).2 hrel
      obtain ⟨q, hq, hqs⟩ := ir_y_cross (g := G) hw1 hw2 e2 (by linarith)
      rw [Geometry.segment_comm] at hq
      exact ⟨_, Or.inr rfl, q, hq, by rw [e]; exact hqs⟩)
  intro z hz
  obtain ⟨g, hg, hgz⟩ := hcov z hz
  rcases hg with rfl | rfl
  · exact Or.inl hgz
  · exact Or.inr hgz

/-- The needle of the x-input of `invRevLe`, hanging from the pocket wall `I Q`:
`m₁ = (G + 60, −59/3)`, tip `(G + 60, −59/3 − H)`, `m₂ = (G + 241/4, −937/48)`. -/
noncomputable def irNeedle (G H : ℝ) : Polygon :=
  tri (G + 60, -59 / 3) (G + 60, -59 / 3 - H) (G + 241 / 4, -937 / 48)

/-- **The x-guard of `invRevLe` sees its needle** (hanging from the pocket wall): through the
corridor, the mouth, the sub-quadrilateral `P, m₁, m₂, Q` of the pocket and the needle mouth. -/
theorem ir_needle_sees {A : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hfA : segment (irP G) (irQ' G) ⊆ A) (hBP : piece (irCorridor G) ⊆ P.filled)
    (hCP : piece (irPocket G) ⊆ P.filled) {H : ℝ} (hH : 0 < H)
    (hNP : piece (irNeedle G H) ⊆ P.filled) {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hxA : inPt (G + 60) v ∈ A) :
    ∀ z ∈ piece (irNeedle G H), P.Sees (inPt (G + 60) v) z := by
  intro z hz
  set g := inPt (G + 60) v with hg
  have hg1 : g.1 = G + 60 := rfl
  have hg2 : g.2 = 4 * v - 2 := rfl
  -- the segment `g z` crosses the needle mouth `m₂ m₁`
  obtain ⟨q₁, hq₁, hq₁z⟩ := cross_tri (a := (G + 60, -59 / 3)) (b := (G + 60, -59 / 3 - H))
    (c := (G + 241 / 4, -937 / 48)) (g := g) (by unfold det; simp only; nlinarith)
    (by unfold det; simp only; rw [hg1]; nlinarith)
    (by unfold det; simp only; rw [hg1, hg2]; nlinarith)
    (by unfold det; simp only; rw [hg1, hg2]; nlinarith) hz
  -- the sub-quadrilateral `P, m₁, m₂, Q` of the pocket
  set K := quad (irP G) (G + 60, -59 / 3) (G + 241 / 4, -937 / 48) (irQ G) with hK
  have hKC : piece K ⊆ piece (irPocket G) := by
    intro x hx
    obtain ⟨k1, k2, k3, k4⟩ := mem_piece_quad.1 hx
    simp only [det, irP, irQ] at k1 k2 k3 k4
    refine mem_piece_quad.2 ⟨?_, ?_, ?_, ?_⟩ <;> simp only [det, irI, irQ, irP, irJ] <;>
      linarith
  have hq₁K : q₁ ∈ piece K := by
    have hc : Convex ℝ (piece K) := convex_piece K
    have hm1 : ((G + 60 : ℝ), (-59 / 3 : ℝ)) ∈ piece K := by
      refine mem_piece_quad.2 ⟨?_, ?_, ?_, ?_⟩ <;> simp only [det, irP, irQ] <;> linarith
    have hm2 : ((G + 241 / 4 : ℝ), (-937 / 48 : ℝ)) ∈ piece K := by
      refine mem_piece_quad.2 ⟨?_, ?_, ?_, ?_⟩ <;> simp only [det, irP, irQ] <;> linarith
    exact Geometry.segment_subset_of_convex hc hm2 hm1 hq₁
  -- the segment `g q₁` crosses the mouth `Q P`
  obtain ⟨q₂, hq₂, hq₂q⟩ := cross_quad (a := irP G) (b := (G + 60, -59 / 3))
    (c := (G + 241 / 4, -937 / 48)) (d := irQ G) (g := g)
    (by simp only [det, irP, irQ]; nlinarith) (by simp only [det, irP, irQ]; nlinarith)
    (by simp only [det, irP]; rw [hg1, hg2]; nlinarith)
    (by simp only [det, irQ]; rw [hg1, hg2]; nlinarith)
    (by simp only [det, irP, irQ]; rw [hg1, hg2]; nlinarith) hq₁K
  rw [Geometry.segment_comm] at hq₂
  have hgq₂ : P.Sees g q₂ := ir_corridor_sees_x hA hAP hfA hBP hv1 hxA q₂
    (ir_mouth_subset_corridor hq₂)
  have hgq₁ : P.Sees g q₁ := sees_via (convex_piece _) hCP hq₂q hgq₂
    (ir_mouth_subset_pocket hq₂) (hKC hq₁K)
  have hq₁N : q₁ ∈ piece (irNeedle G H) := by
    have hD : 0 < det (G + 60, -59 / 3) (G + 60, -59 / 3 - H) (G + 241 / 4, -937 / 48) := by
      unfold det; simp only; nlinarith
    have := edge_subset_piece (isPiece_tri hD) (j := 2) (by simp [tri_n])
    rw [(tri_edge _ _ _).2.2] at this
    exact this hq₁
  exact sees_via (convex_piece _) hNP hq₁z hgq₁ hq₁N hz

end ArtGallery.Stade

end
