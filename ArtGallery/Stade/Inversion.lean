module

public import ArtGallery.Stade.InversionAlg
public import ArtGallery.Stade.Copy

/-!
# Stade construction, §6: the inversion gadgets (geometry)

Visibility facts for the nooks of the two inversion gadgets of `docs/stade/construction.md` §6
(notation of `ArtGallery/Stade/InversionAlg.lean`, slot origin `G`).  As for the copy nooks
(`Stade/Copy.lean`), the statements are relative to a **room** `R` of the polygon `P` whose door
is the mouth `[P, Q]` and which contains the nook segment `[J, I]` but not the guards:

* for `invGe` the pocket `I, Q, P, J` is a convex piece whose walls `I → Q`, `P → J`, `J → I`
  are edges of the polygon, and `ig_isRoom` produces the room (the `…_of_walls` versions);
* for `invRevLe` the wall `I → Q` carries the needle of the x-input, so the room is the
  sub-polygon `P, J, I, m₁, tip, m₂, Q` (closed by the chord `Q P`); it is obtained from
  `Polygon.isRoom_of_chain` (`Vis/Rooms.lean`) in the assembly.

Main results:
* `ig_x_sees`, `ig_y_sees`, `ir_x_sees`, `ir_y_sees` (L6.2): what each designated guard sees of
  the nook segment;
* `ig_rel_of_cover` (`1 ≤ v_x v_y`), `ir_rel_of_cover` (`v_x (5/2 − v_y) ≤ 1`) (L6.3);
* `ig_viewer_mem_PV`, `ir_viewer_mem_PV` (L6.4): viewers of the nook lie in `igPV` / `irPV`;
* `ig_cover_of_rel`, `ir_cover_of_rel` (L6.5) and the equivalences `ig_cover_iff`,
  `ir_cover_iff`: given convex parts `A` (hall), `B` (corridor), `C` (pocket) of the region, the
  two guards see the whole nook segment iff the relation holds.
-/

@[expose] public section

namespace ArtGallery

namespace Stade

open ArtGallery.Geometry

variable {P : Polygon}

/-! ### Sight lines through three convex parts -/

/-- On a segment `[g, s]` going down (`s.2 < g.2`), a point `q₂` not higher than a point `q₁`
lies on `[q₁, s]`. -/
theorem mem_segment_of_snd_le {g s q₁ q₂ : Point} (hq₁ : q₁ ∈ segment g s)
    (hq₂ : q₂ ∈ segment g s) (hgs : s.2 < g.2) (h : q₂.2 ≤ q₁.2) : q₂ ∈ segment q₁ s := by
  obtain ⟨t₁, ht₁0, ht₁1, rfl⟩ := mem_segment_iff_lerp.1 hq₁
  obtain ⟨t₂, ht₂0, ht₂1, rfl⟩ := mem_segment_iff_lerp.1 hq₂
  simp only [lerp_snd] at h
  have ht : t₁ ≤ t₂ := by nlinarith
  rcases eq_or_lt_of_le ht₁1 with h1 | h1
  · have : t₂ = 1 := by linarith
    subst h1; subst this
    simp only [lerp_one]
    exact left_mem_segment s s
  · refine mem_segment_iff_lerp.2 ⟨(t₂ - t₁) / (1 - t₁), div_nonneg (by linarith) (by linarith),
      (div_le_one (by linarith)).2 (by linarith), ?_⟩
    rw [lerp_lerp_right]
    congr 1
    field_simp
    ring

/-- **Visibility through three convex parts of the region**: `g ∈ A`, the segment `[g, s]`
passes through `q₁ ∈ A ∩ B` and then through `q₂ ∈ B ∩ C`, and `s ∈ C`. -/
theorem sees_of_three_convex {A B C : Set Point} (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hB : Convex ℝ B) (hBP : B ⊆ P.filled) (hC : Convex ℝ C) (hCP : C ⊆ P.filled)
    {g s q₁ q₂ : Point} (hg : g ∈ A) (hq₁A : q₁ ∈ A) (hq₁B : q₁ ∈ B) (hq₂B : q₂ ∈ B)
    (hq₂C : q₂ ∈ C) (hs : s ∈ C) (hq₁ : q₁ ∈ segment g s) (hq₂ : q₂ ∈ segment q₁ s) :
    P.Sees g s :=
  sees_of_mem_segment hq₁ (sees_of_convex hA hAP hg hq₁A)
    (sees_of_two_convex hB hC hBP hCP hq₁B hs hq₂B hq₂C hq₂)

/-! ## `invGe` -/

section invGe

variable {G : ℝ} {R : Set Point}

/-- The nook segment of `invGe`, explicitly. -/
theorem ig_nook_iff {s : Point} :
    s ∈ segment (igJ G) (igI G) ↔ s.2 = -78 ∧ G + 61 ≤ s.1 ∧ s.1 ≤ G + 79 :=
  mem_segment_horiz_iff (by linarith)

/-- **x-guard of `invGe` (L6.2)**: a nook point seen from the x-guard is at or right of
`igShX G v`. -/
theorem ig_x_sees (hR : P.IsRoom R (segment (igP G) (igQ G)))
    (hNR : segment (igJ G) (igI G) ⊆ R) {v : ℝ} (hv : 0 ≤ v) (hxR : inPt (G + 40) v ∉ R)
    {s : Point} (hs : s ∈ segment (igJ G) (igI G)) (hsees : P.Sees (inPt (G + 40) v) s) :
    igShX G v ≤ s.1 := by
  obtain ⟨q, hq, hqs⟩ := cross_of_sees_room hR (hNR hs) hxR hsees
  obtain ⟨h1, -, h3⟩ := ig_nook_iff.1 hs
  have e : s = (s.1, -78) := Prod.ext rfl h1
  rw [e] at hqs
  exact ig_x_seen hv h3 hq hqs

/-- **y-guard of `invGe` (L6.2)**: a nook point seen from the y-guard is at or left of
`igShY G w`. -/
theorem ig_y_sees (hR : P.IsRoom R (segment (igP G) (igQ G)))
    (hNR : segment (igJ G) (igI G) ⊆ R) {w : ℝ} (hw : 0 ≤ w) (hyR : inPt (G + 100) w ∉ R)
    {s : Point} (hs : s ∈ segment (igJ G) (igI G)) (hsees : P.Sees (inPt (G + 100) w) s) :
    s.1 ≤ igShY G w := by
  obtain ⟨q, hq, hqs⟩ := cross_of_sees_room hR (hNR hs) hyR hsees
  obtain ⟨h1, h2, -⟩ := ig_nook_iff.1 hs
  have e : s = (s.1, -78) := Prod.ext rfl h1
  rw [e] at hqs
  exact ig_y_seen hw h2 hq hqs

/-- **`invGe`: coverage ⇒ `1 ≤ v_x v_y` (L6.3).** -/
theorem ig_rel_of_cover (hR : P.IsRoom R (segment (igP G) (igQ G)))
    (hNR : segment (igJ G) (igI G) ⊆ R) {v w : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2) (hxR : inPt (G + 40) v ∉ R) (hyR : inPt (G + 100) w ∉ R)
    (hcov : ∀ s ∈ segment (igJ G) (igI G), P.Sees (inPt (G + 40) v) s ∨
      P.Sees (inPt (G + 100) w) s) : 1 ≤ v * w := by
  refine ig_rel_of_shadows (g := G) hv1 hv2 hw1 hw2 (fun h hh1 hh2 => ?_)
  have hs : ((h, -78) : Point) ∈ segment (igJ G) (igI G) := ig_nook_iff.2 ⟨rfl, hh1, hh2⟩
  rcases hcov _ hs with h' | h'
  · exact Or.inl (ig_x_sees hR hNR (by linarith) hxR hs h')
  · exact Or.inr (ig_y_sees hR hNR (by linarith) hyR hs h')

/-- **Viewers of the `invGe` nook (L6.4)**: a point outside the room that sees a point of the
nook segment lies in `igPV`. -/
theorem ig_viewer_mem_PV (hR : P.IsRoom R (segment (igP G) (igQ G)))
    (hNR : segment (igJ G) (igI G) ⊆ R) {s p : Point} (hs : s ∈ segment (igJ G) (igI G))
    (hpR : p ∉ R) (hsees : P.Sees p s) : p ∈ igPV G := by
  obtain ⟨q, hq, hqs⟩ := cross_of_sees_room hR (hNR hs) hpR hsees
  rw [Geometry.segment_comm] at hqs
  exact mem_igPV_of_cross hs hq hqs

/-- The floor crossing of a sight line of the x-guard. -/
theorem ig_x_floor {v h : ℝ} (hv1 : 1 / 2 ≤ v) (hh1 : igShX G v ≤ h)
    (hh2 : h ≤ G + 79) :
    ∃ q₁ ∈ segment (igC1 G) (igC2 G), q₁ ∈ segment (inPt (G + 40) v) (h, -78) := by
  set t := (4 * v - 1) / (4 * v + 76) with ht
  have hd : 0 < 4 * v + 76 := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).2 (by linarith)
  refine ⟨lerp (inPt (G + 40) v) (h, -78) t, ?_, lerp_mem_segment _ _ ht0 ht1⟩
  have hv' : 0 < v + 1 := by linarith
  have hX : 3 * v + 57 ≤ (h - G - 40) * (v + 1) := by
    unfold igShX at hh1
    have : 54 / (v + 1) ≤ h - G - 43 := by linarith
    rw [div_le_iff₀ hv'] at this
    linarith
  have hkey : 2 * (v + 19) ≤ (h - G - 40) * (4 * v - 1) := by
    have h4 : 0 < 4 * v - 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hX h4.le]
  unfold igC1 igC2
  rw [mem_segment_horiz_iff (by linarith)]
  simp only [lerp_fst, lerp_snd, inPt_fst, inPt_snd]
  refine ⟨?_, ?_, ?_⟩
  · rw [ht]; field_simp; ring
  · rw [ht]
    have : (1 : ℝ) / 2 ≤ (4 * v - 1) / (4 * v + 76) * (h - (G + 40)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd]; nlinarith
    linarith
  · rw [ht]
    have : (4 * v - 1) / (4 * v + 76) * (h - (G + 40)) ≤ 59 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hd]; nlinarith
    linarith

/-- The floor crossing of a sight line of the y-guard. -/
theorem ig_y_floor {w h : ℝ} (hw1 : 1 / 2 ≤ w) (hh1 : G + 61 ≤ h)
    (hh2 : h ≤ igShY G w) :
    ∃ q₁ ∈ segment (igC1 G) (igC2 G), q₁ ∈ segment (inPt (G + 100) w) (h, -78) := by
  set t := (4 * w - 1) / (4 * w + 76) with ht
  have hd : 0 < 4 * w + 76 := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).2 (by linarith)
  refine ⟨lerp (inPt (G + 100) w) (h, -78) t, ?_, lerp_mem_segment _ _ ht0 ht1⟩
  have hw' : 0 < w + 1 := by linarith
  have hX : 3 * w + 57 ≤ (G + 100 - h) * (w + 1) := by
    unfold igShY at hh2
    have : 54 / (w + 1) ≤ G + 97 - h := by linarith
    rw [div_le_iff₀ hw'] at this
    linarith
  have hkey : 2 * (w + 19) ≤ (G + 100 - h) * (4 * w - 1) := by
    have h4 : 0 < 4 * w - 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hX h4.le]
  unfold igC1 igC2
  rw [mem_segment_horiz_iff (by linarith)]
  simp only [lerp_fst, lerp_snd, inPt_fst, inPt_snd]
  refine ⟨?_, ?_, ?_⟩
  · rw [ht]; field_simp; ring
  · rw [ht]
    have : (4 * w - 1) / (4 * w + 76) * (G + 100 - h) ≤ 59 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hd]; nlinarith
    have e : (4 * w - 1) / (4 * w + 76) * (h - (G + 100)) =
        -((4 * w - 1) / (4 * w + 76) * (G + 100 - h)) := by ring
    rw [e]; linarith
  · rw [ht]
    have : (1 : ℝ) / 2 ≤ (4 * w - 1) / (4 * w + 76) * (G + 100 - h) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd]; nlinarith
    have e : (4 * w - 1) / (4 * w + 76) * (h - (G + 100)) =
        -((4 * w - 1) / (4 * w + 76) * (G + 100 - h)) := by ring
    rw [e]; linarith

section Positive

variable {A B C : Set Point}

/-- **`invGe`: `1 ≤ v_x v_y` ⇒ coverage (L6.5).**  `A` (hall) contains both guards and the floor
opening `[(G + 81/2, −1), (G + 199/2, −1)]`, `B` (corridor) contains the floor opening and the
mouth, `C` (pocket) contains the mouth and the nook segment; all three are convex parts of the
region. -/
theorem ig_cover_of_rel (hA : Convex ℝ A) (hAP : A ⊆ P.filled) (hB : Convex ℝ B)
    (hBP : B ⊆ P.filled) (hC : Convex ℝ C) (hCP : C ⊆ P.filled)
    (hfA : segment (igC1 G) (igC2 G) ⊆ A) (hfB : segment (igC1 G) (igC2 G) ⊆ B)
    (hmB : segment (igP G) (igQ G) ⊆ B) (hmC : segment (igP G) (igQ G) ⊆ C)
    (hNC : segment (igJ G) (igI G) ⊆ C) {v w : ℝ} (hv1 : 1 / 2 ≤ v) (_hv2 : v ≤ 2)
    (hw1 : 1 / 2 ≤ w) (_hw2 : w ≤ 2) (hxA : inPt (G + 40) v ∈ A) (hyA : inPt (G + 100) w ∈ A)
    (hrel : 1 ≤ v * w) :
    ∀ s ∈ segment (igJ G) (igI G), P.Sees (inPt (G + 40) v) s ∨
      P.Sees (inPt (G + 100) w) s := by
  intro s hs
  obtain ⟨h1, h2, h3⟩ := ig_nook_iff.1 hs
  have e : s = (s.1, -78) := Prod.ext rfl h1
  have hmouth : ∀ q ∈ segment (igP G) (igQ G), q.2 = -6 := fun q hq =>
    ((mem_segment_horiz_iff (by linarith)).1 hq).1
  by_cases hsh : igShX G v ≤ s.1
  · left
    obtain ⟨q₂, hq₂, hq₂s⟩ := ig_x_cross (g := G) hv1 hsh h3
    obtain ⟨q₁, hq₁, hq₁s⟩ := ig_x_floor (G := G) hv1 hsh h3
    have hq₁2 : q₁.2 = -1 := ((mem_segment_horiz_iff (by linarith)).1 hq₁).1
    rw [e]
    refine sees_of_three_convex hA hAP hB hBP hC hCP hxA (hfA hq₁) (hfB hq₁) (hmB hq₂)
      (hmC hq₂) (by rw [← e]; exact hNC hs) hq₁s ?_
    exact mem_segment_of_snd_le hq₁s hq₂s (by simp; linarith)
      (by rw [hmouth q₂ hq₂, hq₁2]; norm_num)
  · right
    push Not at hsh
    have hle := (igSh_le_iff (g := G) (by linarith) (by linarith)).2 hrel
    have hsy : s.1 ≤ igShY G w := by linarith
    obtain ⟨q₂, hq₂, hq₂s⟩ := ig_y_cross (g := G) hw1 h2 hsy
    obtain ⟨q₁, hq₁, hq₁s⟩ := ig_y_floor (G := G) hw1 h2 hsy
    have hq₁2 : q₁.2 = -1 := ((mem_segment_horiz_iff (by linarith)).1 hq₁).1
    rw [e]
    refine sees_of_three_convex hA hAP hB hBP hC hCP hyA (hfA hq₁) (hfB hq₁) (hmB hq₂)
      (hmC hq₂) (by rw [← e]; exact hNC hs) hq₁s ?_
    exact mem_segment_of_snd_le hq₁s hq₂s (by simp; linarith)
      (by rw [hmouth q₂ hq₂, hq₁2]; norm_num)

/-- **`invGe`: the nook is covered iff `1 ≤ v_x v_y`.** -/
theorem ig_cover_iff (hR : P.IsRoom R (segment (igP G) (igQ G)))
    (hNR : segment (igJ G) (igI G) ⊆ R) (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hB : Convex ℝ B) (hBP : B ⊆ P.filled) (hC : Convex ℝ C) (hCP : C ⊆ P.filled)
    (hfA : segment (igC1 G) (igC2 G) ⊆ A) (hfB : segment (igC1 G) (igC2 G) ⊆ B)
    (hmB : segment (igP G) (igQ G) ⊆ B) (hmC : segment (igP G) (igQ G) ⊆ C)
    (hNC : segment (igJ G) (igI G) ⊆ C) {v w : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2) (hxR : inPt (G + 40) v ∉ R) (hyR : inPt (G + 100) w ∉ R)
    (hxA : inPt (G + 40) v ∈ A) (hyA : inPt (G + 100) w ∈ A) :
    (∀ s ∈ segment (igJ G) (igI G), P.Sees (inPt (G + 40) v) s ∨
      P.Sees (inPt (G + 100) w) s) ↔ 1 ≤ v * w :=
  ⟨ig_rel_of_cover hR hNR hv1 hv2 hw1 hw2 hxR hyR,
    ig_cover_of_rel hA hAP hB hBP hC hCP hfA hfB hmB hmC hNC hv1 hv2 hw1 hw2 hxA hyA⟩

end Positive

/-! ### The `invGe` pocket as a room -/

/-- The `invGe` pocket `I, Q, P, J` (counter-clockwise; walls `I → Q`, `P → J`, `J → I`, mouth
`Q → P`), in the vertex convention `lo, dn, up, hi` of `Stade/Exit.lean`. -/
noncomputable def igPocket (G : ℝ) : Polygon := quad (igI G) (igQ G) (igP G) (igJ G)

/-- The `invGe` pocket is strictly convex and counter-clockwise. -/
theorem ig_pocket_ccw :
    0 < det (igI G) (igQ G) (igP G) ∧ 0 < det (igQ G) (igP G) (igJ G) ∧
      0 < det (igP G) (igJ G) (igI G) ∧ 0 < det (igJ G) (igI G) (igQ G) := by
  unfold det igI igQ igP igJ
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring_nf <;> norm_num

/-- The `invGe` pocket is a convex piece. -/
theorem igPocket_isPiece : IsPiece (igPocket G) := by
  obtain ⟨h1, h2, h3, h4⟩ := ig_pocket_ccw (G := G)
  exact isPiece_quad h1 h2 h3 h4

/-- **The `invGe` pocket is a room** with door `[P, Q]`, if its walls `I → Q`, `P → J`, `J → I`
are edges of `P`. -/
theorem ig_isRoom {Pg : Polygon} (hP : Pg.Simple) (hL : Pg.InteriorLeft)
    (hw0 : ∃ i < Pg.n, Pg.vtx i = igI G ∧ Pg.vtx ((i + 1) % Pg.n) = igQ G)
    (hw2 : ∃ i < Pg.n, Pg.vtx i = igP G ∧ Pg.vtx ((i + 1) % Pg.n) = igJ G)
    (hw3 : ∃ i < Pg.n, Pg.vtx i = igJ G ∧ Pg.vtx ((i + 1) % Pg.n) = igI G) :
    Pg.IsRoom (piece (igPocket G)) (segment (igP G) (igQ G)) := by
  have h : Pg.IsRoom (piece (quad (igI G) (igQ G) (igP G) (igJ G)))
      (door (quad (igI G) (igQ G) (igP G) (igJ G)) (· = 1)) :=
    isRoom_piece hP hL igPocket_isPiece (pocket_hWO hw0 hw2 hw3)
  rw [door_quad_one, Geometry.segment_comm] at h
  exact h

/-- The `invGe` nook segment lies in the pocket piece. -/
theorem ig_nook_subset_pocket : segment (igJ G) (igI G) ⊆ piece (igPocket G) := by
  intro s hs
  refine edge_subset_piece igPocket_isPiece (j := 3) (by simp [igPocket, quad, Polygon.n]) ?_
  simpa [Polygon.edge, igPocket, quad, Polygon.vtx, Polygon.n] using hs

/-- Points above the mouth line are not in the `invGe` pocket piece. -/
theorem not_mem_igPocket {p : Point} (hp : -6 < p.2) : p ∉ piece (igPocket G) := by
  intro h
  have h1 := (mem_piece_quad.1 h).2.1
  unfold det igQ igP at h1
  simp only at h1
  nlinarith

/-- **`invGe`, walls form**: if the pocket walls are edges of `P` and the two guards see every
point of the nook segment, then `1 ≤ v_x v_y`. -/
theorem ig_rel_of_walls (hP : P.Simple) (hL : P.InteriorLeft)
    (hw0 : ∃ i < P.n, P.vtx i = igI G ∧ P.vtx ((i + 1) % P.n) = igQ G)
    (hw2 : ∃ i < P.n, P.vtx i = igP G ∧ P.vtx ((i + 1) % P.n) = igJ G)
    (hw3 : ∃ i < P.n, P.vtx i = igJ G ∧ P.vtx ((i + 1) % P.n) = igI G) {v w : ℝ}
    (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) (hw1 : 1 / 2 ≤ w) (hw2' : w ≤ 2)
    (hcov : ∀ s ∈ segment (igJ G) (igI G), P.Sees (inPt (G + 40) v) s ∨
      P.Sees (inPt (G + 100) w) s) : 1 ≤ v * w :=
  ig_rel_of_cover (ig_isRoom hP hL hw0 hw2 hw3) ig_nook_subset_pocket hv1 hv2 hw1 hw2'
    (not_mem_igPocket (by simp; linarith)) (not_mem_igPocket (by simp; linarith)) hcov

/-- **Viewers of the `invGe` nook, walls form**: a point above the mouth line that sees a point
of the nook segment lies in `igPV`. -/
theorem ig_viewer_mem_PV_of_walls (hP : P.Simple) (hL : P.InteriorLeft)
    (hw0 : ∃ i < P.n, P.vtx i = igI G ∧ P.vtx ((i + 1) % P.n) = igQ G)
    (hw2 : ∃ i < P.n, P.vtx i = igP G ∧ P.vtx ((i + 1) % P.n) = igJ G)
    (hw3 : ∃ i < P.n, P.vtx i = igJ G ∧ P.vtx ((i + 1) % P.n) = igI G) {s p : Point}
    (hs : s ∈ segment (igJ G) (igI G)) (hp : -6 < p.2) (hsees : P.Sees p s) : p ∈ igPV G :=
  ig_viewer_mem_PV (ig_isRoom hP hL hw0 hw2 hw3) ig_nook_subset_pocket hs (not_mem_igPocket hp)
    hsees

end invGe

/-! ## `invRevLe` -/

section invRevLe

variable {G : ℝ} {R : Set Point}

/-- The nook segment of `invRevLe`, explicitly. -/
theorem ir_nook_iff {s : Point} :
    s ∈ segment (irJ G) (irI G) ↔ s.2 = -22 ∧ G + 38 ≤ s.1 ∧ s.1 ≤ G + 56 :=
  mem_segment_horiz_iff (by linarith)

/-- **x-guard of `invRevLe` (L6.2)**: a nook point seen from the x-guard is at or right of
`irShX G v`. -/
theorem ir_x_sees (hR : P.IsRoom R (segment (irP G) (irQ G)))
    (hNR : segment (irJ G) (irI G) ⊆ R) {v : ℝ} (hv : 1 / 2 ≤ v) (hxR : inPt (G + 60) v ∉ R)
    {s : Point} (hs : s ∈ segment (irJ G) (irI G)) (hsees : P.Sees (inPt (G + 60) v) s) :
    irShX G v ≤ s.1 := by
  obtain ⟨q, hq, hqs⟩ := cross_of_sees_room hR (hNR hs) hxR hsees
  obtain ⟨h1, -, h3⟩ := ir_nook_iff.1 hs
  have e : s = (s.1, -22) := Prod.ext rfl h1
  rw [e] at hqs
  exact ir_x_seen hv h3 hq hqs

/-- **y-guard of `invRevLe` (L6.2)**: a nook point seen from the y-guard is at or left of
`irShY G w`. -/
theorem ir_y_sees (hR : P.IsRoom R (segment (irP G) (irQ G)))
    (hNR : segment (irJ G) (irI G) ⊆ R) {w : ℝ} (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2)
    (hyR : inPt (G + 104) w ∉ R) {s : Point} (hs : s ∈ segment (irJ G) (irI G))
    (hsees : P.Sees (inPt (G + 104) w) s) : s.1 ≤ irShY G w := by
  obtain ⟨q, hq, hqs⟩ := cross_of_sees_room hR (hNR hs) hyR hsees
  obtain ⟨h1, h2, -⟩ := ir_nook_iff.1 hs
  have e : s = (s.1, -22) := Prod.ext rfl h1
  rw [e] at hqs
  exact ir_y_seen hw1 hw2 h2 hq hqs

/-- **`invRevLe`: coverage ⇒ `v_x (5/2 − v_y) ≤ 1` (L6.3).** -/
theorem ir_rel_of_cover (hR : P.IsRoom R (segment (irP G) (irQ G)))
    (hNR : segment (irJ G) (irI G) ⊆ R) {v w : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2) (hxR : inPt (G + 60) v ∉ R) (hyR : inPt (G + 104) w ∉ R)
    (hcov : ∀ s ∈ segment (irJ G) (irI G), P.Sees (inPt (G + 60) v) s ∨
      P.Sees (inPt (G + 104) w) s) : v * (5 / 2 - w) ≤ 1 := by
  refine ir_rel_of_shadows (g := G) hv1 hv2 hw1 hw2 (fun h hh1 hh2 => ?_)
  have hs : ((h, -22) : Point) ∈ segment (irJ G) (irI G) := ir_nook_iff.2 ⟨rfl, hh1, hh2⟩
  rcases hcov _ hs with h' | h'
  · exact Or.inl (ir_x_sees hR hNR hv1 hxR hs h')
  · exact Or.inr (ir_y_sees hR hNR hw1 hw2 hyR hs h')

/-- **Viewers of the `invRevLe` nook (L6.4)**: a point outside the room that sees a point of the
nook segment lies in `irPV`. -/
theorem ir_viewer_mem_PV (hR : P.IsRoom R (segment (irP G) (irQ G)))
    (hNR : segment (irJ G) (irI G) ⊆ R) {s p : Point} (hs : s ∈ segment (irJ G) (irI G))
    (hpR : p ∉ R) (hsees : P.Sees p s) : p ∈ irPV G := by
  obtain ⟨q, hq, hqs⟩ := cross_of_sees_room hR (hNR hs) hpR hsees
  rw [Geometry.segment_comm] at hqs
  exact mem_irPV_of_cross hs hq hqs

/-- The floor crossing of a sight line of the x-guard of `invRevLe`. -/
theorem ir_x_floor {v h : ℝ} (hv1 : 1 / 2 ≤ v) (hh1 : irShX G v ≤ h) (hh2 : h ≤ G + 56) :
    ∃ q₁ ∈ segment (irP G) (irQ' G), q₁ ∈ segment (inPt (G + 60) v) (h, -22) := by
  set t := (4 * v - 1) / (4 * v + 20) with ht
  have hd : 0 < 4 * v + 20 := by linarith
  have h4 : 0 < 4 * v - 1 := by linarith
  have ht0 : 0 ≤ t := div_nonneg h4.le hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).2 (by linarith)
  refine ⟨lerp (inPt (G + 60) v) (h, -22) t, ?_, lerp_mem_segment _ _ ht0 ht1⟩
  have hX : (G + 60 - h) * (4 * v - 1) ≤ 4 * v + 20 := by
    unfold irShX at hh1
    have : G + 59 - h ≤ 21 / (4 * v - 1) := by linarith
    rw [le_div_iff₀ h4] at this
    linarith
  unfold irP irQ'
  rw [mem_segment_horiz_iff (by linarith)]
  simp only [lerp_fst, lerp_snd, inPt_fst, inPt_snd]
  have e : (4 * v - 1) / (4 * v + 20) * (h - (G + 60)) =
      -((4 * v - 1) / (4 * v + 20) * (G + 60 - h)) := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [ht]; field_simp; ring
  · rw [ht, e]
    have : (4 * v - 1) / (4 * v + 20) * (G + 60 - h) ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hd]; nlinarith
    linarith
  · rw [ht, e]
    have : 0 ≤ (4 * v - 1) / (4 * v + 20) * (G + 60 - h) :=
      mul_nonneg ht0 (by linarith)
    linarith

/-- The floor crossing of a sight line of the y-guard of `invRevLe`. -/
theorem ir_y_floor {w h : ℝ} (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2) (hh1 : G + 38 ≤ h)
    (hh2 : h ≤ irShY G w) :
    ∃ q₁ ∈ segment (irP G) (irQ' G), q₁ ∈ segment (inPt (G + 104) w) (h, -22) := by
  set t := (4 * w - 1) / (4 * w + 20) with ht
  have hd : 0 < 4 * w + 20 := by linarith
  have h4 : 0 < 4 * w - 1 := by linarith
  have ht0 : 0 ≤ t := div_nonneg h4.le hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).2 (by linarith)
  refine ⟨lerp (inPt (G + 104) w) (h, -22) t, ?_, lerp_mem_segment _ _ ht0 ht1⟩
  have h23 : 0 < 2 * w + 3 := by linarith
  have hX : 12 * (4 * w + 20) ≤ (G + 104 - h) * (2 * w + 3) := by
    unfold irShY at hh2
    have : 168 / (2 * w + 3) ≤ G + 80 - h := by linarith
    rw [div_le_iff₀ h23] at this
    nlinarith
  have hkey : 3 * (4 * w + 20) ≤ (G + 104 - h) * (4 * w - 1) := by
    nlinarith [mul_le_mul_of_nonneg_right hX h4.le]
  unfold irP irQ'
  rw [mem_segment_horiz_iff (by linarith)]
  simp only [lerp_fst, lerp_snd, inPt_fst, inPt_snd]
  have e : (4 * w - 1) / (4 * w + 20) * (h - (G + 104)) =
      -((4 * w - 1) / (4 * w + 20) * (G + 104 - h)) := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [ht]; field_simp; ring
  · rw [ht, e]
    have : (4 * w - 1) / (4 * w + 20) * (G + 104 - h) ≤ 45 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hd]; nlinarith
    linarith
  · rw [ht, e]
    have : 3 ≤ (4 * w - 1) / (4 * w + 20) * (G + 104 - h) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd]; nlinarith
    linarith

section Positive

variable {A B C : Set Point}

/-- **`invRevLe`: `v_x (5/2 − v_y) ≤ 1` ⇒ coverage (L6.5).**  `A` (hall) contains both guards
and the floor opening `[P, Q']`, `B` (the corridor triangle `P, Q, Q'`) contains the floor
opening and the mouth `[P, Q]`, `C` (the pocket `I, Q, P, J`) contains the mouth and the nook
segment; all three are convex parts of the region. -/
theorem ir_cover_of_rel (hA : Convex ℝ A) (hAP : A ⊆ P.filled) (hB : Convex ℝ B)
    (hBP : B ⊆ P.filled) (hC : Convex ℝ C) (hCP : C ⊆ P.filled)
    (hfA : segment (irP G) (irQ' G) ⊆ A) (hfB : segment (irP G) (irQ' G) ⊆ B)
    (hmB : segment (irP G) (irQ G) ⊆ B) (hmC : segment (irP G) (irQ G) ⊆ C)
    (hNC : segment (irJ G) (irI G) ⊆ C) {v w : ℝ} (hv1 : 1 / 2 ≤ v) (_hv2 : v ≤ 2)
    (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2) (hxA : inPt (G + 60) v ∈ A) (hyA : inPt (G + 104) w ∈ A)
    (hrel : v * (5 / 2 - w) ≤ 1) :
    ∀ s ∈ segment (irJ G) (irI G), P.Sees (inPt (G + 60) v) s ∨
      P.Sees (inPt (G + 104) w) s := by
  intro s hs
  obtain ⟨h1, h2, h3⟩ := ir_nook_iff.1 hs
  have e : s = (s.1, -22) := Prod.ext rfl h1
  have hmouth : ∀ q ∈ segment (irP G) (irQ G), q.2 ≤ -1 := fun q hq => by
    have := (affine_of_mem_segment hq Prod.snd (fun t => by simp only [lerp_snd]; ring)).2
    simp only [irP, irQ] at this
    rw [max_eq_left (by norm_num)] at this
    exact this
  by_cases hsh : irShX G v ≤ s.1
  · left
    obtain ⟨q₂, hq₂, hq₂s⟩ := ir_x_cross (g := G) hv1 hsh h3
    obtain ⟨q₁, hq₁, hq₁s⟩ := ir_x_floor (G := G) hv1 hsh h3
    have hq₁2 : q₁.2 = -1 := ((mem_segment_horiz_iff (by linarith)).1 hq₁).1
    rw [e]
    refine sees_of_three_convex hA hAP hB hBP hC hCP hxA (hfA hq₁) (hfB hq₁) (hmB hq₂)
      (hmC hq₂) (by rw [← e]; exact hNC hs) hq₁s ?_
    exact mem_segment_of_snd_le hq₁s hq₂s (by simp; linarith) (by rw [hq₁2]; exact hmouth q₂ hq₂)
  · right
    push Not at hsh
    have hle := (irSh_le_iff (g := G) hv1 (by linarith)).2 hrel
    have hsy : s.1 ≤ irShY G w := by linarith
    obtain ⟨q₂, hq₂, hq₂s⟩ := ir_y_cross (g := G) hw1 hw2 h2 hsy
    obtain ⟨q₁, hq₁, hq₁s⟩ := ir_y_floor (G := G) hw1 hw2 h2 hsy
    have hq₁2 : q₁.2 = -1 := ((mem_segment_horiz_iff (by linarith)).1 hq₁).1
    rw [e]
    refine sees_of_three_convex hA hAP hB hBP hC hCP hyA (hfA hq₁) (hfB hq₁) (hmB hq₂)
      (hmC hq₂) (by rw [← e]; exact hNC hs) hq₁s ?_
    exact mem_segment_of_snd_le hq₁s hq₂s (by simp; linarith) (by rw [hq₁2]; exact hmouth q₂ hq₂)

/-- **`invRevLe`: the nook is covered iff `v_x (5/2 − v_y) ≤ 1`.** -/
theorem ir_cover_iff (hR : P.IsRoom R (segment (irP G) (irQ G)))
    (hNR : segment (irJ G) (irI G) ⊆ R) (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hB : Convex ℝ B) (hBP : B ⊆ P.filled) (hC : Convex ℝ C) (hCP : C ⊆ P.filled)
    (hfA : segment (irP G) (irQ' G) ⊆ A) (hfB : segment (irP G) (irQ' G) ⊆ B)
    (hmB : segment (irP G) (irQ G) ⊆ B) (hmC : segment (irP G) (irQ G) ⊆ C)
    (hNC : segment (irJ G) (irI G) ⊆ C) {v w : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2) (hxR : inPt (G + 60) v ∉ R) (hyR : inPt (G + 104) w ∉ R)
    (hxA : inPt (G + 60) v ∈ A) (hyA : inPt (G + 104) w ∈ A) :
    (∀ s ∈ segment (irJ G) (irI G), P.Sees (inPt (G + 60) v) s ∨
      P.Sees (inPt (G + 104) w) s) ↔ v * (5 / 2 - w) ≤ 1 :=
  ⟨ir_rel_of_cover hR hNR hv1 hv2 hw1 hw2 hxR hyR,
    ir_cover_of_rel hA hAP hB hBP hC hCP hfA hfB hmB hmC hNC hv1 hv2 hw1 hw2 hxA hyA⟩

end Positive

/-- The `invRevLe` pocket `I, Q, P, J` (counter-clockwise; the wall `I → Q` carries the needle
of the x-input) as a piece. -/
noncomputable def irPocket (G : ℝ) : Polygon := quad (irI G) (irQ G) (irP G) (irJ G)

/-- The `invRevLe` pocket is strictly convex and counter-clockwise. -/
theorem ir_pocket_ccw :
    0 < det (irI G) (irQ G) (irP G) ∧ 0 < det (irQ G) (irP G) (irJ G) ∧
      0 < det (irP G) (irJ G) (irI G) ∧ 0 < det (irJ G) (irI G) (irQ G) := by
  unfold det irI irQ irP irJ
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring_nf <;> norm_num

/-- The `invRevLe` pocket is a convex piece (its point set is the convex part `C` of
`ir_cover_of_rel`). -/
theorem irPocket_isPiece : IsPiece (irPocket G) := by
  obtain ⟨h1, h2, h3, h4⟩ := ir_pocket_ccw (G := G)
  exact isPiece_quad h1 h2 h3 h4

end invRevLe

/-! ## The `invRevLe` pocket region as a room -/

section irRoom

open ArtGallery.Stade.Chain ArtGallery.Irrational Set

/-- A point strictly right of a line that has all vertices of `K` weakly on its left is outside
the region of `K`. -/
theorem not_mem_filled_of_right {K : Polygon} {e₀ e₁ : Point} (he : e₀ ≠ e₁)
    (hsupp : ∀ j < K.n, 0 ≤ det e₀ e₁ (K.vtx j)) {x : Point} (hx : det e₀ e₁ x < 0) :
    x ∉ K.filled := by
  have hsq := Jordan.sqLen_pos he
  have hbd : ∀ y ∈ K.boundary, 0 ≤ det e₀ e₁ y := by
    rintro y ⟨j, hj, τ, hτ0, hτ1, rfl⟩
    have h1 := hsupp j hj
    have h2 := hsupp _ (Nat.mod_lt _ (by omega) : (j + 1) % K.n < K.n)
    show 0 ≤ det e₀ e₁ (lerp (K.vtx j) (K.vtx ((j + 1) % K.n)) τ)
    rw [det_lerp]
    nlinarith [mul_nonneg hτ0 h2, mul_nonneg (sub_nonneg.2 hτ1) h1]
  have hxb : x ∉ K.boundary := fun h => by linarith [hbd x h]
  intro hxf
  rw [Jordan.mem_filled_iff_bounded K hxb] at hxf
  set d : Point := (e₁.2 - e₀.2, -(e₁.1 - e₀.1)) with hd
  have hdet : ∀ s : ℝ, det e₀ e₁ (x + s • d) = det e₀ e₁ x - s * Jordan.sqLen e₀ e₁ := by
    intro s; simp only [hd, det, Jordan.sqLen, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]; ring
  have hd0 : d ≠ 0 := by
    intro h0
    have := hdet 1
    rw [h0, smul_zero, add_zero] at this
    linarith
  refine Jordan.not_isBoundedSet_connectedComponentIn_of_ray K hd0 ?_ hxf
  rintro _ ⟨s, hs, rfl⟩ hp
  have h1 := hbd _ hp
  rw [hdet] at h1
  nlinarith [mul_nonneg (mem_Ici.1 hs) hsq.le]

/-- The pocket chain of `invRevLe`: `P, J, I, m₁, tip, m₂, Q`. -/
def irPocketChain : List RPt :=
  [(59, -1, 0), (38, -22, 0), (56, -22, 0), (60, -59 / 3, 0), (60, -59 / 3, 1),
    (241 / 4, -937 / 48, 0), (80, -8, 0)]

/-- The pocket chain is robustly simple for `H ≥ 1000` (verified checker). -/
theorem irPocketChain_ok : rChainB 1000 irPocketChain = true := by decide +kernel


/-- `det` of three instantiated template vertices. -/
theorem det_inst (H ox : ℚ) (a b c : RPt) :
    det (ratPoint (a.inst H ox)) (ratPoint (b.inst H ox)) (ratPoint (c.inst H ox)) =
      ((rdetA a b c + rdetB a b c * H : ℚ) : ℝ) := by
  rw [Irrational.det_ratPoint, qdet_inst]

/-- A point of a segment `[u, w]` on the line `z a`, with `u, w` weakly left of it and one of
them strictly, is an end point. -/
theorem eq_of_mem_segment_det {z a u w x : Point} (hx : x ∈ segment u w) (hu : 0 ≤ det z a u)
    (hw : 0 ≤ det z a w) (hxd : det z a x = 0) (hpos : 0 < det z a u ∨ 0 < det z a w) :
    x = u ∨ x = w := by
  obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_lerp.1 hx
  rw [det_lerp] at hxd
  rcases hpos with h | h
  · right
    have : t = 1 := by nlinarith [mul_nonneg ht0 hw]
    subst this; simp
  · left
    have : t = 0 := by nlinarith [mul_nonneg (sub_nonneg.2 ht1) hu]
    subst this; simp

/-- The `invRevLe` pocket polygon `P, J, I, m₁, tip, m₂, Q` (parameter `H`, translation `ox`). -/
noncomputable def irK (H ox : ℚ) : Polygon := ⟨rpts H ox irPocketChain⟩

/-- The pocket polygon has `7` vertices. -/
theorem irK_n (H ox : ℚ) : (irK H ox).n = 7 := rfl

/-- The chord `Q → P` of the `invRevLe` pocket: `det Q P x = −7 ((x.1 − ox) + 3 x.2 − 56)`. -/
theorem ir_chord_det (H ox : ℚ) (p : RPt) :
    det (ratPoint (RPt.inst H ox (80, -8, 0))) (ratPoint (RPt.inst H ox (59, -1, 0)))
      (ratPoint (RPt.inst H ox p)) = -7 * ((p.1 : ℝ) + 3 * ((p.2.1 : ℝ) - p.2.2 * H) - 56) := by
  rw [det_inst]; simp only [rdetA, rdetB]; push_cast; ring

/-- The supporting-edge signs: every vertex of the `invRevLe` pocket polygon is weakly left of
the chord `Q → P`. -/
theorem irK_det {H ox : ℚ} (hH : 1000 ≤ H) :
    ∀ i < 7, 0 ≤ det ((irK H ox).vtx 6) ((irK H ox).vtx 0) ((irK H ox).vtx i) := by
  have hH' : (1000 : ℝ) ≤ H := by exact_mod_cast hH
  intro i hi
  interval_cases i <;> (simp only [irK, Polygon.vtx, rpts, irPocketChain, List.map_cons,
    List.map_nil, List.getD_cons_succ, List.getD_cons_zero]; rw [ir_chord_det]; norm_num)
  all_goals nlinarith

/-- The `invRevLe` pocket polygon is simple for `H ≥ 1000`. -/
theorem irK_simple {H ox : ℚ} (hH : 1000 ≤ H) : (irK H ox).Simple := by
  have hH' : (1000 : ℝ) ≤ H := by exact_mod_cast hH
  have hc := rChainB_sound (ox := ox) hH irPocketChain_ok
  show (Polygon.mk (_ :: [_, _, _, _, _] ++ [_])).Simple
  refine simple_of_chain (by simp) hc ?_
  rintro x ⟨hx1, hx2⟩
  have hx0 := det_eq_zero_of_mem_segment hx1
  beta_reduce at hx0 hx2 ⊢
  have v1 : det (ratPoint (RPt.inst H ox (80, -8, 0))) (ratPoint (RPt.inst H ox (59, -1, 0)))
      (ratPoint (RPt.inst H ox (38, -22, 0))) = 588 := by rw [ir_chord_det]; norm_num
  have v2 : det (ratPoint (RPt.inst H ox (80, -8, 0))) (ratPoint (RPt.inst H ox (59, -1, 0)))
      (ratPoint (RPt.inst H ox (56, -22, 0))) = 462 := by rw [ir_chord_det]; norm_num
  have v3 : det (ratPoint (RPt.inst H ox (80, -8, 0))) (ratPoint (RPt.inst H ox (59, -1, 0)))
      (ratPoint (RPt.inst H ox (60, -59 / 3, 0))) = 385 := by rw [ir_chord_det]; norm_num
  have v4 : det (ratPoint (RPt.inst H ox (80, -8, 0))) (ratPoint (RPt.inst H ox (59, -1, 0)))
      (ratPoint (RPt.inst H ox (60, -59 / 3, 1))) = 385 + 21 * H := by
    rw [ir_chord_det]; norm_num; ring
  have v5 : det (ratPoint (RPt.inst H ox (80, -8, 0))) (ratPoint (RPt.inst H ox (59, -1, 0)))
      (ratPoint (RPt.inst H ox (241 / 4, -937 / 48, 0))) = 6083 / 16 := by
    rw [ir_chord_det]; norm_num
  simp only [List.cons_append, List.nil_append, chainSet_cons_cons, chainSet_single,
    Set.union_empty, Set.mem_union] at hx2
  rcases hx2 with h | h | h | h | h | h
  · rcases eq_of_mem_segment_det h (by simp) (by rw [v1]; norm_num) hx0
      (Or.inr (by rw [v1]; norm_num)) with e | e
    · left; exact e
    · exfalso; rw [e, v1] at hx0; norm_num at hx0
  · rcases eq_of_mem_segment_det h (by rw [v1]; norm_num) (by rw [v2]; norm_num) hx0
      (Or.inr (by rw [v2]; norm_num)) with e | e
    · exfalso; rw [e, v1] at hx0; norm_num at hx0
    · exfalso; rw [e, v2] at hx0; norm_num at hx0
  · rcases eq_of_mem_segment_det h (by rw [v2]; norm_num) (by rw [v3]; norm_num) hx0
      (Or.inr (by rw [v3]; norm_num)) with e | e
    · exfalso; rw [e, v2] at hx0; norm_num at hx0
    · exfalso; rw [e, v3] at hx0; norm_num at hx0
  · rcases eq_of_mem_segment_det h (by rw [v3]; norm_num) (by rw [v4]; nlinarith) hx0
      (Or.inl (by rw [v3]; norm_num)) with e | e
    · exfalso; rw [e, v3] at hx0; norm_num at hx0
    · exfalso; rw [e, v4] at hx0; nlinarith
  · rcases eq_of_mem_segment_det h (by rw [v4]; nlinarith) (by rw [v5]; norm_num) hx0
      (Or.inr (by rw [v5]; norm_num)) with e | e
    · exfalso; rw [e, v4] at hx0; nlinarith
    · exfalso; rw [e, v5] at hx0; norm_num at hx0
  · rcases eq_of_mem_segment_det h (by rw [v5]; norm_num) (by simp) hx0
      (Or.inl (by rw [v5]; norm_num)) with e | e
    · exfalso; rw [e, v5] at hx0; norm_num at hx0
    · right; exact e

/-- The `invRevLe` pocket polygon is counter-clockwise. -/
theorem irK_interiorLeft {H ox : ℚ} (hH : 1000 ≤ H) : (irK H ox).InteriorLeft :=
  Polygon.interiorLeft_of_supporting_edge (irK_simple hH) (i := 6) (by rw [irK_n]; norm_num)
    (fun j hj => by
      have e : (6 + 1) % (irK H ox).n = 0 := by rw [irK_n]
      rw [e]
      rw [irK_n] at hj
      exact irK_det hH j hj)

/-- Vertex `0` of the pocket polygon is `P`. -/
theorem irK_vtx0 (H ox : ℚ) : (irK H ox).vtx 0 = irP (ox : ℝ) := by
  simp only [irK, Polygon.vtx, rpts, irPocketChain, List.map_cons, List.getD_cons_zero,
    RPt.inst, ratPoint, irP]
  push_cast; ring_nf

/-- Vertex `1` of the pocket polygon is `J`. -/
theorem irK_vtx1 (H ox : ℚ) : (irK H ox).vtx 1 = irJ (ox : ℝ) := by
  simp only [irK, Polygon.vtx, rpts, irPocketChain, List.map_cons, List.getD_cons_succ,
    List.getD_cons_zero, RPt.inst, ratPoint, irJ]
  push_cast; ring_nf

/-- Vertex `2` of the pocket polygon is `I`. -/
theorem irK_vtx2 (H ox : ℚ) : (irK H ox).vtx 2 = irI (ox : ℝ) := by
  simp only [irK, Polygon.vtx, rpts, irPocketChain, List.map_cons, List.getD_cons_succ,
    List.getD_cons_zero, RPt.inst, ratPoint, irI]
  push_cast; ring_nf

/-- Vertex `6` of the pocket polygon is `Q`. -/
theorem irK_vtx6 (H ox : ℚ) : (irK H ox).vtx 6 = irQ (ox : ℝ) := by
  simp only [irK, Polygon.vtx, rpts, irPocketChain, List.map_cons, List.getD_cons_succ,
    List.getD_cons_zero, RPt.inst, ratPoint, irQ]
  push_cast; ring_nf


/-- The chord `Q P` is non-degenerate. -/
theorem irK_ne (H ox : ℚ) : (irK H ox).vtx 6 ≠ (irK H ox).vtx 0 := by
  rw [irK_vtx6, irK_vtx0]
  intro h
  have := congrArg Prod.snd h
  simp [irQ, irP] at this

/-- **The `invRevLe` pocket is a room** of `P` with door `[P, Q]`: if the vertices
`P, J, I, m₁, tip, m₂, Q` of the gadget chain are consecutive vertices `a, …, a + 6` of `P`
(indices mod `P.n`), then the region of the pocket polygon `irK H ox` is a room. -/
theorem ir_isRoom (hP : P.Simple) (hL : P.InteriorLeft) {H ox : ℚ} (hH : 1000 ≤ H) {a : ℕ}
    (hchain : ∀ j ≤ 6, (irK H ox).vtx j = P.vtx ((a + j) % P.n)) :
    P.IsRoom (irK H ox).filled (segment (irP (ox : ℝ)) (irQ (ox : ℝ))) := by
  have h := Polygon.isRoom_of_chain hP hL (irK_simple hH) (irK_interiorLeft hH)
    (irK_n H ox : (irK H ox).n = 6 + 1) hchain
  rwa [irK_vtx6, irK_vtx0, Geometry.segment_comm] at h

/-- The `invRevLe` nook segment lies in the pocket region. -/
theorem ir_nook_subset_irK (H ox : ℚ) :
    segment (irJ (ox : ℝ)) (irI (ox : ℝ)) ⊆ (irK H ox).filled := by
  intro x hx
  refine Or.inl ⟨1, by rw [irK_n]; norm_num, ?_⟩
  have e : (1 + 1) % (irK H ox).n = 2 := by rw [irK_n]
  show x ∈ segment ((irK H ox).vtx 1) ((irK H ox).vtx ((1 + 1) % (irK H ox).n))
  rw [e, irK_vtx1, irK_vtx2]
  exact hx

/-- Points strictly beyond the mouth line (`x − ox + 3y > 56`), e.g. all points of the hall
with `y ≥ −1` and `x ≥ ox + 60`, are not in the `invRevLe` pocket region. -/
theorem not_mem_irK {H ox : ℚ} (hH : 1000 ≤ H) {p : Point} (hp : 56 < p.1 - ox + 3 * p.2) :
    p ∉ (irK H ox).filled := by
  refine not_mem_filled_of_right (irK_ne H ox) (fun j hj => irK_det hH j (by rwa [irK_n] at hj))
    ?_
  rw [irK_vtx6, irK_vtx0]
  unfold det irQ irP
  simp only
  nlinarith

/-- **`invRevLe`, chain form**: if the pocket chain `P, J, I, m₁, tip, m₂, Q` is a contiguous
part of the boundary of `P` and the two guards see every point of the nook segment, then
`v_x (5/2 − v_y) ≤ 1`. -/
theorem ir_rel_of_chain (hP : P.Simple) (hL : P.InteriorLeft) {H ox : ℚ} (hH : 1000 ≤ H)
    {a : ℕ} (hchain : ∀ j ≤ 6, (irK H ox).vtx j = P.vtx ((a + j) % P.n)) {v w : ℝ}
    (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2)
    (hcov : ∀ s ∈ segment (irJ (ox : ℝ)) (irI (ox : ℝ)), P.Sees (inPt ((ox : ℝ) + 60) v) s ∨
      P.Sees (inPt ((ox : ℝ) + 104) w) s) : v * (5 / 2 - w) ≤ 1 :=
  ir_rel_of_cover (ir_isRoom hP hL hH hchain) (ir_nook_subset_irK H ox) hv1 hv2 hw1 hw2
    (not_mem_irK hH (by simp; linarith)) (not_mem_irK hH (by simp; linarith)) hcov

/-- **Viewers of the `invRevLe` nook, chain form**: a point beyond the mouth line that sees a
point of the nook segment lies in `irPV`. -/
theorem ir_viewer_mem_PV_of_chain (hP : P.Simple) (hL : P.InteriorLeft) {H ox : ℚ}
    (hH : 1000 ≤ H) {a : ℕ} (hchain : ∀ j ≤ 6, (irK H ox).vtx j = P.vtx ((a + j) % P.n))
    {s p : Point} (hs : s ∈ segment (irJ (ox : ℝ)) (irI (ox : ℝ)))
    (hp : 56 < p.1 - ox + 3 * p.2) (hsees : P.Sees p s) : p ∈ irPV (ox : ℝ) :=
  ir_viewer_mem_PV (ir_isRoom hP hL hH hchain) (ir_nook_subset_irK H ox) hs (not_mem_irK hH hp)
    hsees

end irRoom

/-! ## Corridors and pockets as convex pieces (for the positive direction) -/

section Pieces

variable {G : ℝ}

/-- The `invGe` corridor `(G + 81/2, −1), P, Q, (G + 199/2, −1)` (counter-clockwise). -/
noncomputable def igCorridor (G : ℝ) : Polygon := quad (igC1 G) (igP G) (igQ G) (igC2 G)

/-- The `invGe` corridor is a convex piece. -/
theorem igCorridor_isPiece : IsPiece (igCorridor G) := by
  refine isPiece_quad ?_ ?_ ?_ ?_ <;> simp only [det, igC1, igP, igQ, igC2] <;> ring_nf <;> norm_num

/-- The floor opening of the `invGe` corridor lies in the corridor piece. -/
theorem ig_floor_subset_corridor : segment (igC1 G) (igC2 G) ⊆ piece (igCorridor G) := by
  intro x hx
  refine edge_subset_piece igCorridor_isPiece (j := 3) (by simp [igCorridor, quad, Polygon.n]) ?_
  rw [Geometry.segment_comm] at hx
  simpa [Polygon.edge, igCorridor, quad, Polygon.vtx, Polygon.n] using hx

/-- The mouth of the `invGe` pocket lies in the corridor piece. -/
theorem ig_mouth_subset_corridor : segment (igP G) (igQ G) ⊆ piece (igCorridor G) := by
  intro x hx
  refine edge_subset_piece igCorridor_isPiece (j := 1) (by simp [igCorridor, quad, Polygon.n]) ?_
  simpa [Polygon.edge, igCorridor, quad, Polygon.vtx, Polygon.n] using hx

/-- The mouth of the `invGe` pocket lies in the pocket piece. -/
theorem ig_mouth_subset_pocket : segment (igP G) (igQ G) ⊆ piece (igPocket G) := by
  intro x hx
  refine edge_subset_piece igPocket_isPiece (j := 1) (by simp [igPocket, quad, Polygon.n]) ?_
  rw [Geometry.segment_comm] at hx
  simpa [Polygon.edge, igPocket, quad, Polygon.vtx, Polygon.n] using hx

/-- The `invRevLe` corridor triangle `P, Q, Q'` (counter-clockwise). -/
noncomputable def irCorridor (G : ℝ) : Polygon := tri (irP G) (irQ G) (irQ' G)

/-- The `invRevLe` corridor is a convex piece. -/
theorem irCorridor_isPiece : IsPiece (irCorridor G) := by
  refine isPiece_tri ?_
  unfold det irP irQ irQ'; ring_nf; norm_num

/-- The floor opening `[P, Q']` of the `invRevLe` corridor lies in the corridor piece. -/
theorem ir_floor_subset_corridor : segment (irP G) (irQ' G) ⊆ piece (irCorridor G) := by
  intro x hx
  refine edge_subset_piece irCorridor_isPiece (j := 2) (by simp [irCorridor, tri, Polygon.n]) ?_
  rw [Geometry.segment_comm] at hx
  simpa [Polygon.edge, irCorridor, tri, Polygon.vtx, Polygon.n] using hx

/-- The mouth of the `invRevLe` pocket lies in the corridor piece. -/
theorem ir_mouth_subset_corridor : segment (irP G) (irQ G) ⊆ piece (irCorridor G) := by
  intro x hx
  refine edge_subset_piece irCorridor_isPiece (j := 0) (by simp [irCorridor, tri, Polygon.n]) ?_
  simpa [Polygon.edge, irCorridor, tri, Polygon.vtx, Polygon.n] using hx

/-- The mouth of the `invRevLe` pocket lies in the (convex) pocket piece. -/
theorem ir_mouth_subset_pocket : segment (irP G) (irQ G) ⊆ piece (irPocket G) := by
  intro x hx
  refine edge_subset_piece irPocket_isPiece (j := 1) (by simp [irPocket, quad, Polygon.n]) ?_
  rw [Geometry.segment_comm] at hx
  simpa [Polygon.edge, irPocket, quad, Polygon.vtx, Polygon.n] using hx

/-- The `invRevLe` nook segment lies in the (convex) pocket piece. -/
theorem ir_nook_subset_pocket : segment (irJ G) (irI G) ⊆ piece (irPocket G) := by
  intro x hx
  refine edge_subset_piece irPocket_isPiece (j := 3) (by simp [irPocket, quad, Polygon.n]) ?_
  simpa [Polygon.edge, irPocket, quad, Polygon.vtx, Polygon.n] using hx

end Pieces

/-! ## Interface with the templates (`Templates.lean`) -/

/-- The `invGe` gadget chain of `Templates.lean`, translated by `ox`, is
`(ox + 81/2, −1), P, J, I, Q, (ox + 199/2, −1)`. -/
theorem chainInvGe_inst (H ox : ℚ) :
    chainInvGe.map (fun p => ratPoint (p.inst H ox)) =
      [igC1 (ox : ℝ), igP (ox : ℝ), igJ (ox : ℝ), igI (ox : ℝ), igQ (ox : ℝ), igC2 (ox : ℝ)] := by
  simp only [chainInvGe, List.map_cons, List.map_nil, Chain.RPt.inst, ratPoint, igC1, igP, igJ, igI,
    igQ, igC2]
  push_cast
  norm_num

/-- The `invRevLe` gadget chain of `Templates.lean`, translated by `ox`, is
`P, J, I, m₁, tip, m₂, Q, Q'` (the needle of the x-input hangs from the wall `I Q`). -/
theorem chainInvRevLe_inst (H ox : ℚ) :
    chainInvRevLe.map (fun p => ratPoint (p.inst H ox)) =
      [irP (ox : ℝ), irJ (ox : ℝ), irI (ox : ℝ), ((ox : ℝ) + 60, -59 / 3),
        ((ox : ℝ) + 60, -59 / 3 - (H : ℝ)), ((ox : ℝ) + 241 / 4, -937 / 48), irQ (ox : ℝ),
        irQ' (ox : ℝ)] := by
  simp only [chainInvRevLe, List.map_cons, List.map_nil, Chain.RPt.inst, ratPoint, irP, irJ, irI,
    irQ, irQ']
  push_cast
  norm_num

/-- The `invRevLe` gadget chain is the pocket chain followed by the corridor corner `Q'`. -/
theorem chainInvRevLe_eq : chainInvRevLe = irPocketChain ++ [(101, -1, 0)] := rfl

end Stade

end ArtGallery

end
