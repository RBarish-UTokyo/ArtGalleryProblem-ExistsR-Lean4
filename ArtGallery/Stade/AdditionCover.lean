module

public import ArtGallery.Stade.AdditionGeom

/-!
# Stade construction, §7: positive visibility in the addition gadgets (generic part, `addLe`)

For statement (b) of the reduction every point of the region must be seen.  This file proves,
for `addLe` with the aux guard at the canonical point `I = alI G v_x v_y` and the inputs at their
values (proof plan L7.8):

* `al_pocketX_cover`, `al_pocketY_cover`, `al_pocketZ_cover` (**chords argument**): every point
  of each pocket (not only of the nook segment) is seen by the aux guard or by the input of the
  pocket (for the z-pocket: if `v_x + v_y ≤ v_z`);
* `al_aux_sees_room`, `al_aux_sees_auxTri`: the aux guard (any point of the aux region above the
  bottom) sees the room and the aux wedge;
* `al_needleX_seen`, `al_needleY_seen`: the inputs standing above the window see their needles
  hanging from the bottom of the room.

Generic tools: `add_det_nonneg_tri`, `add_det_nonneg_quad` (an affine functional `det A B ·`
nonnegative at the vertices of a triangle / convex quadrilateral is nonnegative on it),
`add_chord` and `add_pocket_split` (the chord argument: the chord from the mouth corner `dn`
through the shadow `s*` of the first guard splits the pocket into the part seen by the first
guard and the part seen by the second one), `add_sees_vmouth`, `add_sees_window_vmouth`,
`add_sees_tri_through`, `add_sees_window_tri` (sight lines through a vertical mouth, through the
window and a vertical mouth, into a triangle through one of its sides).
-/

@[expose] public section

namespace ArtGallery

namespace Stade

open ArtGallery.Geometry

variable {P : Polygon}

/-! ## Generic tools -/

/-- The barycentric expansion of the affine functional `det A B ·` on the triangle `a b c`. -/
theorem add_det_bary (a b c x A B : Point) :
    det a b c * det A B x =
      det b c x * det A B a + det c a x * det A B b + det a b x * det A B c := by
  unfold det; ring

/-- An affine functional `det A B ·` nonnegative at the vertices of a counter-clockwise triangle
is nonnegative on the triangle. -/
theorem add_det_nonneg_tri {a b c x A B : Point} (habc : 0 < det a b c)
    (hx : x ∈ piece (tri a b c)) (ha : 0 ≤ det A B a) (hb : 0 ≤ det A B b)
    (hc : 0 ≤ det A B c) : 0 ≤ det A B x := by
  obtain ⟨h0, h1, h2⟩ := mem_piece_tri.1 hx
  have key : 0 ≤ det a b c * det A B x := by
    rw [add_det_bary]
    exact add_nonneg (add_nonneg (mul_nonneg h1 ha) (mul_nonneg h2 hb)) (mul_nonneg h0 hc)
  by_contra hneg
  push Not at hneg
  nlinarith [mul_neg_of_pos_of_neg habc hneg]

/-- An affine functional `det A B ·` nonnegative at the vertices of a strictly convex
counter-clockwise quadrilateral is nonnegative on it. -/
theorem add_det_nonneg_quad {lo dn up hi x A B : Point} (h1 : 0 < det lo dn up)
    (h3 : 0 < det up hi lo) (hx : x ∈ piece (quad lo dn up hi)) (hlo : 0 ≤ det A B lo)
    (hdn : 0 ≤ det A B dn) (hup : 0 ≤ det A B up) (hhi : 0 ≤ det A B hi) : 0 ≤ det A B x := by
  obtain ⟨q0, q1, q2, q3⟩ := mem_piece_quad.1 hx
  rcases le_total 0 (det lo up x) with h | h
  · have e : det lo up hi = det up hi lo := (det_cyclic lo up hi).symm
    exact add_det_nonneg_tri (by rw [e]; exact h3) (mem_piece_tri.2 ⟨h, q2, q3⟩) hlo hup hhi
  · have e : det up lo x = -det lo up x := det_swap12 lo up x
    exact add_det_nonneg_tri h1 (mem_piece_tri.2 ⟨q0, q1, by rw [e]; linarith⟩) hlo hdn hup

/-- `det A B ·` vanishes at `B`. -/
theorem add_det_self (A B : Point) : det A B B = 0 := by unfold det; ring

/-- Crossing a segment: `g` and `x` strictly on opposite sides of `O₁ O₂`, `x` in the closed
double cone at `g` spanned by `O₁, O₂`. -/
theorem add_cross {g x O₁ O₂ : Point} (hg : det O₁ O₂ g < 0) (hx : 0 < det O₁ O₂ x)
    (hc : det g O₁ x * det g O₂ x ≤ 0) : ∃ q ∈ segment O₁ O₂, q ∈ segment g x :=
  exists_cross_of_det_mul_det_nonpos (mul_neg_of_neg_of_pos hg hx) hc

/-- The mouth corner `O` lies on the segment from `g` to its shadow `(c, π_O(g))`. -/
theorem add_lerp_vproj {g O : Point} {c : ℝ} (hO : O.1 ≠ g.1) (hc : c ≠ g.1) :
    O = lerp g (c, vproj g O c) ((O.1 - g.1) / (c - g.1)) := by
  have h1 : O.1 - g.1 ≠ 0 := sub_ne_zero.2 hO
  have h2 : c - g.1 ≠ 0 := sub_ne_zero.2 hc
  ext
  · simp only [lerp_fst]; field_simp; ring
  · simp only [lerp_snd, vproj]; field_simp; ring

/-- **The chord argument.**  Let `lo, dn, up, hi` be a strictly convex counter-clockwise pocket,
`s` a point of `[lo, hi]` and `dn` a point strictly between `g` and `s`.  A point `p` of the
pocket strictly on the `lo`-side of the chord `dn s` (`0 < det g dn p`) lies in the triangle
`lo, dn, s`; hence an affine functional nonnegative at `lo, dn, s` is nonnegative at `p`. -/
theorem add_chord {lo dn up hi g s : Point} (h4 : 0 < det hi lo dn) {σ θ : ℝ} (hσ0 : 0 ≤ σ)
    (hs : s = lerp lo hi σ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hdn : dn = lerp g s θ) {A B : Point}
    (hlo : 0 ≤ det A B lo) (hdn' : 0 ≤ det A B dn) (hs' : 0 ≤ det A B s) {p : Point}
    (hp : p ∈ piece (quad lo dn up hi)) (hcase : 0 < det g dn p) : 0 ≤ det A B p := by
  obtain ⟨q0, -, -, q3⟩ := mem_piece_quad.1 hp
  have e0 : det g g p = 0 := by unfold det; ring
  have e0' : det s s p = 0 := by unfold det; ring
  have e1 : det g dn p = θ * det g s p := by
    rw [hdn, det_lerp_mid, e0]; ring
  have e2 : det dn s p = (1 - θ) * det g s p := by
    rw [hdn, det_lerp_left, e0']; ring
  have hgs : 0 < det g s p := by
    rw [e1] at hcase; exact pos_of_mul_pos_right hcase hθ0.le
  have hds : 0 < det dn s p := by rw [e2]; exact mul_pos (by linarith) hgs
  have e3 : det s lo p = σ * det hi lo p := by
    have : det lo lo p = 0 := by unfold det; ring
    rw [hs, det_lerp_left, this]; ring
  rcases eq_or_lt_of_le hσ0 with hσ | hσ
  · exfalso
    subst hσ
    have : s = lo := by rw [hs]; exact lerp_zero lo hi
    rw [this, det_swap12] at hds
    linarith
  · have hD : 0 < det lo dn s := by
      have e0 : det lo dn lo = 0 := by unfold det; ring
      have e : det lo dn hi = det hi lo dn := (det_cyclic_right lo dn hi).symm
      rw [hs, det_lerp, e0, e]
      nlinarith
    exact add_det_nonneg_tri hD (mem_piece_tri.2 ⟨q0, hds.le, by rw [e3]; positivity⟩) hlo hdn'
      hs'

/-- **Splitting a pocket between two guards.**  Pocket `lo, dn, up, hi` (strictly convex,
counter-clockwise) with nook segment `[lo, hi]` on `x = c` (`lo` below `hi`) and `dn` right of
it.  The guard `ga` (right of `dn`) has its shadow `s* = (c, π_dn(ga))` on the nook segment and
the whole pocket below its line through `up`; the guard `gb` has the whole pocket above its line
through `dn`, and `lo, dn, s*` below its line through `up`.  Then every point of the pocket lies
in the cone of `ga` or in the cone of `gb` through the mouth `[dn, up]`. -/
theorem add_pocket_split {lo dn up hi ga gb : Point} (h1 : 0 < det lo dn up)
    (h3 : 0 < det up hi lo) (h4 : 0 < det hi lo dn) {c : ℝ} (hlo : lo.1 = c) (hhi : hi.1 = c)
    (hlh : lo.2 < hi.2) (hc : c < dn.1) (hga : dn.1 < ga.1) (hs1 : lo.2 ≤ vproj ga dn c)
    (ha_lo : 0 ≤ det ga up lo) (ha_dn : 0 ≤ det ga up dn) (ha_hi : 0 ≤ det ga up hi)
    (hb_lo : det gb dn lo ≤ 0) (hb_up : det gb dn up ≤ 0) (hb_hi : det gb dn hi ≤ 0)
    (hb_lo' : 0 ≤ det gb up lo) (hb_dn' : 0 ≤ det gb up dn)
    (hb_s : 0 ≤ det gb up (c, vproj ga dn c)) {p : Point} (hp : p ∈ piece (quad lo dn up hi)) :
    (det ga dn p ≤ 0 ∧ 0 ≤ det ga up p) ∨ (det gb dn p ≤ 0 ∧ 0 ≤ det gb up p) := by
  have hA : 0 ≤ det ga up p := add_det_nonneg_quad h1 h3 hp ha_lo ha_dn (add_det_self _ _).ge ha_hi
  have hB : det gb dn p ≤ 0 := by
    have sw : ∀ x, det dn gb x = -det gb dn x := fun x => det_swap12 gb dn x
    have := add_det_nonneg_quad (A := dn) (B := gb) h1 h3 hp (by rw [sw]; linarith)
      (by rw [sw, add_det_self]; simp) (by rw [sw]; linarith) (by rw [sw]; linarith)
    rw [sw] at this; linarith
  by_cases hcase : det ga dn p ≤ 0
  · exact Or.inl ⟨hcase, hA⟩
  · right
    push Not at hcase
    refine ⟨hB, ?_⟩
    have hd : hi.2 - lo.2 ≠ 0 := by linarith
    have hs : ((c, vproj ga dn c) : Point) = lerp lo hi ((vproj ga dn c - lo.2) / (hi.2 - lo.2)) := by
      ext
      · simp only [lerp_fst]; rw [hlo, hhi]; ring
      · simp only [lerp_snd]; field_simp; ring
    have hθ0 : 0 < (dn.1 - ga.1) / (c - ga.1) := div_pos_of_neg_of_neg (by linarith) (by linarith)
    have hθ1 : (dn.1 - ga.1) / (c - ga.1) < 1 := (div_lt_one_of_neg (by linarith)).2 (by linarith)
    exact add_chord h4 (div_nonneg (by linarith) (by linarith)) hs hθ0 hθ1
      (add_lerp_vproj hga.ne (by linarith)) hb_lo' hb_dn' hb_s hp hcase

section Sight

variable {A B C : Set Point}

/-- **Sight line through a vertical mouth.**  `a ∈ B` right of the mouth `[(d, yd), (d, yu)]`
(contained in `B` and in `C`), `p ∈ C` at or left of `x = d` (on the mouth if on its line), in
the cone of `a` spanned by the mouth: `a` sees `p`. -/
theorem add_sees_vmouth (hB : Convex ℝ B) (hBP : B ⊆ P.filled) (hC : Convex ℝ C)
    (hCP : C ⊆ P.filled) {d yd yu : ℝ} (hyd : yd < yu)
    (hmB : ∀ q : Point, q.1 = d → yd ≤ q.2 → q.2 ≤ yu → q ∈ B)
    (hmC : segment ((d, yd) : Point) (d, yu) ⊆ C) {a p : Point} (ha : a ∈ B) (had : d < a.1)
    (hp : p ∈ C) (hpd : p.1 ≤ d) (hpl : p.1 = d → yd ≤ p.2 ∧ p.2 ≤ yu)
    (h1 : det a (d, yd) p ≤ 0) (h2 : 0 ≤ det a (d, yu) p) : P.Sees a p := by
  rcases eq_or_lt_of_le hpd with he | hlt
  · obtain ⟨l1, l2⟩ := hpl he
    exact sees_of_convex hB hBP ha (hmB p he l1 l2)
  · obtain ⟨q, hq, hqp⟩ := add_cross (O₁ := ((d, yd) : Point)) (O₂ := (d, yu)) (g := a) (x := p)
      (by simp only [det]; nlinarith [mul_pos (sub_pos.2 had) (sub_pos.2 hyd)])
      (by simp only [det]; nlinarith [mul_pos (sub_pos.2 hlt) (sub_pos.2 hyd)])
      (mul_nonpos_of_nonpos_of_nonneg h1 h2)
    obtain ⟨e1, e2, e3⟩ := (mem_segment_vert_iff hyd.le).1 hq
    exact sees_of_two_convex hB hC hBP hCP ha hp (hmB q e1 e2 e3) (hmC hq) hqp

/-- The crossing with the window `[(x₁, −1), (x₂, −1)]` of a sight line from `g` (above the
floor) to `p` (below), in the cone of `g` spanned by the window. -/
theorem add_cross_window {x₁ x₂ : ℝ} (hx : x₁ < x₂) {g p : Point} (hg2 : -1 < g.2)
    (hp2 : p.2 < -1) (hw1 : 0 ≤ det g (x₁, -1) p) (hw2 : det g (x₂, -1) p ≤ 0) :
    ∃ q : Point, q ∈ segment g p ∧ q.2 = -1 ∧ x₁ ≤ q.1 ∧ q.1 ≤ x₂ := by
  obtain ⟨q, hq, hqp⟩ := add_cross (O₁ := ((x₂, -1) : Point)) (O₂ := (x₁, -1)) (g := g) (x := p)
    (by simp only [det]; nlinarith [mul_pos (sub_pos.2 hx) (sub_pos.2 hg2)])
    (by simp only [det]; nlinarith [mul_pos (sub_pos.2 hx) (sub_pos.2 hp2)])
    (mul_nonpos_of_nonpos_of_nonneg hw2 hw1)
  rw [segment_comm] at hq
  obtain ⟨e1, e2, e3⟩ := (mem_segment_horiz_iff hx.le).1 hq
  exact ⟨q, hqp, e1, e2, e3⟩

/-- **Sight line through the window and a vertical mouth.**  `g ∈ A` above the floor, the window
`[(x₁, −1), (x₂, −1)]` in `A ∩ B`, then as in `add_sees_vmouth`. -/
theorem add_sees_window_vmouth (hA : Convex ℝ A) (hAP : A ⊆ P.filled) (hB : Convex ℝ B)
    (hBP : B ⊆ P.filled) (hC : Convex ℝ C) (hCP : C ⊆ P.filled) {x₁ x₂ : ℝ} (hx : x₁ < x₂)
    (hwA : ∀ q : Point, q.2 = -1 → x₁ ≤ q.1 → q.1 ≤ x₂ → q ∈ A ∧ q ∈ B) {d yd yu : ℝ}
    (hyd : yd < yu) (hyu : yu < -1)
    (hmB : ∀ q : Point, q.1 = d → yd ≤ q.2 → q.2 ≤ yu → q ∈ B)
    (hmC : segment ((d, yd) : Point) (d, yu) ⊆ C) {g p : Point} (hg : g ∈ A) (hg2 : -1 < g.2)
    (hgd : d < g.1) (hp : p ∈ C) (hpd : p.1 ≤ d) (hpl : p.1 = d → yd ≤ p.2 ∧ p.2 ≤ yu)
    (hp2 : p.2 < -1) (hw1 : 0 ≤ det g (x₁, -1) p) (hw2 : det g (x₂, -1) p ≤ 0)
    (h1 : det g (d, yd) p ≤ 0) (h2 : 0 ≤ det g (d, yu) p) : P.Sees g p := by
  obtain ⟨q₁, hq₁, e1, e2, e3⟩ := add_cross_window hx hg2 hp2 hw1 hw2
  obtain ⟨hq₁A, hq₁B⟩ := hwA q₁ e1 e2 e3
  rcases eq_or_lt_of_le hpd with he | hlt
  · obtain ⟨l1, l2⟩ := hpl he
    exact sees_of_two_convex hA hB hAP hBP hg (hmB p he l1 l2) hq₁A hq₁B hq₁
  · obtain ⟨q₂, hq₂, hq₂p⟩ := add_cross (O₁ := ((d, yd) : Point)) (O₂ := (d, yu)) (g := g)
      (x := p) (by simp only [det]; nlinarith [mul_pos (sub_pos.2 hgd) (sub_pos.2 hyd)])
      (by simp only [det]; nlinarith [mul_pos (sub_pos.2 hlt) (sub_pos.2 hyd)])
      (mul_nonpos_of_nonpos_of_nonneg h1 h2)
    obtain ⟨f1, f2, f3⟩ := (mem_segment_vert_iff hyd.le).1 hq₂
    refine add_sees_chain3 hA hAP hB hBP hC hCP hg hq₁A hq₁B (hmB q₂ f1 f2 f3) (hmC hq₂) hp hq₁
      ?_
    exact add_mem_segment_of_snd_le hq₁ hq₂p (by linarith) (by rw [e1]; linarith)

/-- **Seeing a triangle through one of its sides.**  `g ∈ B` (convex), strictly beyond the side
`[c, a]` of the counter-clockwise triangle `a b c` (contained in `B`), with `b` in the cone of
`g` spanned by `c, a`: `g` sees the whole triangle. -/
theorem add_sees_tri_through {a b c g : Point} (habc : 0 < det a b c) (hB : Convex ℝ B)
    (hBP : B ⊆ P.filled) (hTP : piece (tri a b c) ⊆ P.filled) (hgB : g ∈ B)
    (hmB : segment c a ⊆ B) (hg : det c a g < 0) (hcb : det g c b ≤ 0) (hab : 0 ≤ det g a b)
    {x : Point} (hx : x ∈ piece (tri a b c)) : P.Sees g x := by
  obtain ⟨t0, t1, t2⟩ := mem_piece_tri.1 hx
  have hgca : det g c a = det c a g := (det_cyclic g c a).symm
  have hc1 : det g c x ≤ 0 := by
    have sw : ∀ y, det c g y = -det g c y := fun y => det_swap12 g c y
    have := add_det_nonneg_tri (A := c) (B := g) habc hx (by rw [sw]; linarith)
      (by rw [sw]; linarith) (by rw [sw, add_det_self]; simp)
    rw [sw] at this; linarith
  have hc2 : 0 ≤ det g a x := by
    have e : det g a c = -det g c a := det_swap23 g c a
    exact add_det_nonneg_tri habc hx (add_det_self _ _).ge hab (by rw [e]; linarith)
  rcases eq_or_lt_of_le t2 with h0 | hpos
  · -- `x` on the side `[c, a]`
    have hb := det_smul_eq_bary_combination a b c x
    have e1 : det x b c = det b c x := det_cyclic_right b c x
    have hsum := det_bary_sum a b c x
    have e3 : det a x c = 0 := by
      have : det c a x = det a x c := det_cyclic_right a x c
      rw [← this]; exact h0.symm
    have hx1 := congrArg Prod.fst hb
    have hx2 := congrArg Prod.snd hb
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul] at hx1 hx2
    rw [e1, e3] at hx1 hx2
    rw [e1, e3] at hsum
    have hD : det a b c ≠ 0 := habc.ne'
    have hab' : det a b x = det a b c - det b c x := by linarith
    have hxs : x ∈ segment c a := by
      refine mem_segment_iff_lerp.2 ⟨det b c x / det a b c, div_nonneg t1 habc.le, ?_, ?_⟩
      · rw [div_le_one habc]; linarith
      · have f1 : x.1 = (det b c x * a.1 + det a b x * c.1) / det a b c := by
          field_simp; linarith
        have f2 : x.2 = (det b c x * a.2 + det a b x * c.2) / det a b c := by
          field_simp; linarith
        ext
        · simp only [lerp_fst]; rw [f1, hab']; field_simp; ring
        · simp only [lerp_snd]; rw [f2, hab']; field_simp; ring
    exact sees_of_convex hB hBP hgB (hmB hxs)
  · obtain ⟨q, hq, hqx⟩ := add_cross hg hpos (mul_nonpos_of_nonpos_of_nonneg hc1 hc2)
    have hqT : q ∈ piece (tri a b c) :=
      edge_subset_piece (isPiece_tri habc) (j := 2) (by simp [tri, Polygon.n])
        (by simpa [Polygon.edge, tri, Polygon.vtx, Polygon.n] using hq)
    exact sees_of_two_convex hB (convex_piece _) hBP hTP hgB hx (hmB hq) hqT hqx

end Sight

/-- Converse sign lemma: a nook point at or below the shadow of `g` through `O` (with `O`
strictly left of `g`) has `0 ≤ det g O (c, h)`. -/
theorem add_det_vert_nonneg {g O : Point} {c h : ℝ} (hO : O.1 < g.1) (hh : h ≤ vproj g O c) :
    0 ≤ det g O (c, h) := by
  rw [det_vert g O c h hO.ne]
  exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

/-- Converse sign lemma: a nook point at or above the shadow has `det g O (c, h) ≤ 0`. -/
theorem add_det_vert_nonpos {g O : Point} {c h : ℝ} (hO : O.1 < g.1) (hh : vproj g O c ≤ h) :
    det g O (c, h) ≤ 0 := by
  rw [det_vert g O c h hO.ne]
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

/-! ## `addLe` -/

section addLe

variable {G : ℝ} {A : Set Point}

/-- The window of `addLe` lies in the hall `A` (if `A` contains it) and in the room. -/
theorem al_window_mem (hWA : segment (alWL G) (alWR G) ⊆ A) :
    ∀ q : Point, q.2 = -1 → G + 200 ≤ q.1 → q.1 ≤ G + 527 → q ∈ A ∧ q ∈ piece (alRoom G) := by
  intro q h1 h2 h3
  have hq : q ∈ segment (alWL G) (alWR G) :=
    (mem_segment_horiz_iff (c := -1) (x₁ := G + 200) (x₂ := G + 527) (by linarith)).2 ⟨h1, h2, h3⟩
  exact ⟨hWA hq, alRoom_window hq⟩

/-- **`addLe`, x-pocket (chords argument).**  With the aux guard at `I(v_x, v_y)` and the
x-input at `v_x`, every point of the x-pocket is seen by one of them. -/
theorem al_pocketX_cover (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (alWL G) (alWR G) ⊆ A) (hRP : piece (alRoom G) ⊆ P.filled)
    (hXP : piece (alPocketX G) ⊆ P.filled) {vx vy : ℝ} (hx1 : 1 / 2 ≤ vx) (hy1 : 1 / 2 ≤ vy)
    (hxy : vx + vy ≤ 2) (hxA : inPt (G + 370) vx ∈ A) :
    ∀ p ∈ piece (alPocketX G), P.Sees (alI G vx vy) p ∨ P.Sees (inPt (G + 370) vx) p := by
  intro p hp
  obtain ⟨c1, c2, c3, c4⟩ := alPocketX_ccw (G := G)
  have hx2 : vx ≤ 2 := by linarith
  have hy0 : (0 : ℝ) ≤ vy := by linarith
  have hIf := alI_fst (G := G) hx2 hy0
  have hI := alI_mem_auxRegion (G := G) hx1 hy1 hxy
  obtain ⟨q0, q1, q2, q3⟩ := mem_piece_quad.1 hp
  simp only [det, alXlo, alP, alN1, alXhi] at q0 q1 q2 q3
  have hpd : p.1 ≤ G + 50 := by nlinarith
  have hpl : p.1 = G + 50 → -113 ≤ p.2 ∧ p.2 ≤ -445 / 4 := fun h => by
    rw [h] at q0 q2; constructor <;> linarith
  have hp2 : p.2 < -1 := by nlinarith
  have hmR : ∀ q : Point, q.1 = G + 50 → -113 ≤ q.2 → q.2 ≤ -445 / 4 → q ∈ piece (alRoom G) :=
    fun q h1 h2 h3 => alRoom_left h1 (by linarith) h3
  have hmC : segment ((G + 50, -113) : Point) (G + 50, -445 / 4) ⊆ piece (alPocketX G) :=
    add_mouth_subset c1 c2 c3 c4
  have hS := al_shadows_mem hx1 hx2
  have hN1 := alI_N1 (G := G) hx1 hx2 hy1
  have hPin := al_input_x_P (G := G) (v := vx) (by linarith)
  have hIP := alI_P (G := G) hx2 hy0
  have hgP : (alP G).1 < (inPt (G + 370) vx).1 := by simp only [alP, inPt_fst]; linarith
  have hlh : (alXlo G).2 < (alXhi G).2 := by simp only [alXlo, alXhi]; norm_num
  have hc : G + 30 < (alP G).1 := by simp only [alP]; linarith
  have hs1 : (alXlo G).2 ≤ vproj (alI G vx vy) (alP G) (G + 30) := by
    rw [hIP]; exact hS.1.1
  have ha_lo : 0 ≤ det (alI G vx vy) (alN1 G) (alXlo G) :=
    add_det_vert_nonneg (c := G + 30) (h := -7589 / 64) hIf (by linarith)
  have ha_dn : 0 ≤ det (alI G vx vy) (alN1 G) (alP G) := by
    simp only [det, alN1, alP]; nlinarith
  have ha_hi : 0 ≤ det (alI G vx vy) (alN1 G) (alXhi G) :=
    add_det_vert_nonneg (c := G + 30) (h := -7561 / 64) hIf (by linarith)
  have hb_lo : det (inPt (G + 370) vx) (alP G) (alXlo G) ≤ 0 :=
    add_det_vert_nonpos (c := G + 30) (h := -7589 / 64) hgP (by linarith)
  have hb_up : det (inPt (G + 370) vx) (alP G) (alN1 G) ≤ 0 := by
    simp only [det, alP, alN1, inPt_fst, inPt_snd]; nlinarith
  have hb_hi : det (inPt (G + 370) vx) (alP G) (alXhi G) ≤ 0 :=
    add_det_vert_nonpos (c := G + 30) (h := -7561 / 64) hgP (by linarith)
  have hb_lo' : 0 ≤ det (inPt (G + 370) vx) (alN1 G) (alXlo G) :=
    add_det_vert_nonneg (c := G + 30) (h := -7589 / 64) hgP (by rw [al_shadow_x]; exact hS.1.1)
  have hb_dn' : 0 ≤ det (inPt (G + 370) vx) (alN1 G) (alP G) := by
    simp only [det, alN1, alP, inPt_fst, inPt_snd]; nlinarith
  have hb_s : 0 ≤ det (inPt (G + 370) vx) (alN1 G) (G + 30, vproj (alI G vx vy) (alP G) (G + 30)) :=
    add_det_vert_nonneg hgP (by rw [hIP, al_shadow_x])
  rcases add_pocket_split (lo := alXlo G) (dn := alP G) (up := alN1 G) (hi := alXhi G)
      (ga := alI G vx vy) (gb := inPt (G + 370) vx) (c := G + 30) c1 c3 c4 rfl rfl hlh hc hIf hs1
      ha_lo ha_dn ha_hi hb_lo hb_up hb_hi hb_lo' hb_dn' hb_s hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (add_sees_vmouth (convex_piece _) hRP (convex_piece _) hXP (by norm_num) hmR hmC
      hI.2 hIf hp hpd hpl h1 h2)
  · refine Or.inr (add_sees_window_vmouth hA hAP (convex_piece _) hRP (convex_piece _) hXP
      (by linarith) (al_window_mem hWA) (by norm_num) (by norm_num) hmR hmC hxA
      (by simp only [inPt_snd]; linarith) hgP hp hpd hpl hp2 ?_ ?_ h1 h2)
    · refine add_det_nonneg_quad c1 c3 hp ?_ ?_ ?_ ?_ <;>
        simp only [det, alXlo, alP, alN1, alXhi, inPt_fst, inPt_snd] <;> linarith
    · have sw : ∀ x, det ((G + 527, -1) : Point) (inPt (G + 370) vx) x =
          -det (inPt (G + 370) vx) (G + 527, -1) x := fun x => det_swap12 _ _ x
      have := add_det_nonneg_quad (A := ((G + 527, -1) : Point)) (B := inPt (G + 370) vx) c1 c3 hp
        (by simp only [det, alXlo, inPt_fst, inPt_snd]; linarith)
        (by simp only [det, alP, inPt_fst, inPt_snd]; linarith)
        (by simp only [det, alN1, inPt_fst, inPt_snd]; linarith)
        (by simp only [det, alXhi, inPt_fst, inPt_snd]; linarith)
      rw [sw] at this; linarith

/-- **`addLe`, y-pocket (chords argument).**  With the aux guard at `I(v_x, v_y)` and the
y-input at `v_y`, every point of the y-pocket is seen by one of them. -/
theorem al_pocketY_cover (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (alWL G) (alWR G) ⊆ A) (hRP : piece (alRoom G) ⊆ P.filled)
    (hYP : piece (alPocketY G) ⊆ P.filled) {vx vy : ℝ} (hx1 : 1 / 2 ≤ vx) (hy1 : 1 / 2 ≤ vy)
    (hxy : vx + vy ≤ 2) (hyA : inPt (G + 210) vy ∈ A) :
    ∀ p ∈ piece (alPocketY G), P.Sees (alI G vx vy) p ∨ P.Sees (inPt (G + 210) vy) p := by
  intro p hp
  obtain ⟨c1, c2, c3, c4⟩ := alPocketY_ccw (G := G)
  have hx2 : vx ≤ 2 := by linarith
  have hy2 : vy ≤ 2 := by linarith
  have hy0 : (0 : ℝ) ≤ vy := by linarith
  have hIf := alI_fst (G := G) hx2 hy0
  have hI := alI_mem_auxRegion (G := G) hx1 hy1 hxy
  obtain ⟨q0, q1, q2, q3⟩ := mem_piece_quad.1 hp
  simp only [det, alYlo, alR, alN3, alYhi] at q0 q1 q2 q3
  have hpd : p.1 ≤ G + 50 := by nlinarith
  have hpl : p.1 = G + 50 → -128 ≤ p.2 ∧ p.2 ≤ -491 / 4 := fun h => by
    rw [h] at q0 q2; constructor <;> linarith
  have hp2 : p.2 < -1 := by nlinarith
  have hmR : ∀ q : Point, q.1 = G + 50 → -128 ≤ q.2 → q.2 ≤ -491 / 4 → q ∈ piece (alRoom G) :=
    fun q h1 h2 h3 => alRoom_left h1 h2 (by linarith)
  have hmC : segment ((G + 50, -128) : Point) (G + 50, -491 / 4) ⊆ piece (alPocketY G) :=
    add_mouth_subset c1 c2 c3 c4
  have hS := al_shadows_mem hy1 hy2
  have hN3 := alI_N3 (G := G) hx1 hx2 hy1 hy2
  have hRin := al_input_y_R (G := G) (v := vy) (by linarith)
  have hIR := alI_R (G := G) hx2 hy0
  have hgR : (alR G).1 < (inPt (G + 210) vy).1 := by simp only [alR, inPt_fst]; linarith
  have hlh : (alYlo G).2 < (alYhi G).2 := by simp only [alYlo, alYhi]; norm_num
  have hc : G + 30 < (alR G).1 := by simp only [alR]; linarith
  have hs1 : (alYlo G).2 ≤ vproj (alI G vx vy) (alR G) (G + 30) := by
    rw [hIR]; exact hS.2.1.1
  have ha_lo : 0 ≤ det (alI G vx vy) (alN3 G) (alYlo G) :=
    add_det_vert_nonneg (c := G + 30) (h := -4443 / 32) hIf (by linarith)
  have ha_dn : 0 ≤ det (alI G vx vy) (alN3 G) (alR G) := by
    simp only [det, alN3, alR]; nlinarith
  have ha_hi : 0 ≤ det (alI G vx vy) (alN3 G) (alYhi G) :=
    add_det_vert_nonneg (c := G + 30) (h := -4417 / 32) hIf (by linarith)
  have hb_lo : det (inPt (G + 210) vy) (alR G) (alYlo G) ≤ 0 :=
    add_det_vert_nonpos (c := G + 30) (h := -4443 / 32) hgR (by linarith)
  have hb_up : det (inPt (G + 210) vy) (alR G) (alN3 G) ≤ 0 := by
    simp only [det, alR, alN3, inPt_fst, inPt_snd]; nlinarith
  have hb_hi : det (inPt (G + 210) vy) (alR G) (alYhi G) ≤ 0 :=
    add_det_vert_nonpos (c := G + 30) (h := -4417 / 32) hgR (by linarith)
  have hb_lo' : 0 ≤ det (inPt (G + 210) vy) (alN3 G) (alYlo G) :=
    add_det_vert_nonneg (c := G + 30) (h := -4443 / 32) hgR (by rw [al_shadow_y]; exact hS.2.1.1)
  have hb_dn' : 0 ≤ det (inPt (G + 210) vy) (alN3 G) (alR G) := by
    simp only [det, alN3, alR, inPt_fst, inPt_snd]; nlinarith
  have hb_s : 0 ≤ det (inPt (G + 210) vy) (alN3 G) (G + 30, vproj (alI G vx vy) (alR G) (G + 30)) :=
    add_det_vert_nonneg hgR (by rw [hIR, al_shadow_y])
  rcases add_pocket_split (lo := alYlo G) (dn := alR G) (up := alN3 G) (hi := alYhi G)
      (ga := alI G vx vy) (gb := inPt (G + 210) vy) (c := G + 30) c1 c3 c4 rfl rfl hlh hc hIf hs1
      ha_lo ha_dn ha_hi hb_lo hb_up hb_hi hb_lo' hb_dn' hb_s hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (add_sees_vmouth (convex_piece _) hRP (convex_piece _) hYP (by norm_num) hmR hmC
      hI.2 hIf hp hpd hpl h1 h2)
  · refine Or.inr (add_sees_window_vmouth hA hAP (convex_piece _) hRP (convex_piece _) hYP
      (by linarith) (al_window_mem hWA) (by norm_num) (by norm_num) hmR hmC hyA
      (by simp only [inPt_snd]; linarith) hgR hp hpd hpl hp2 ?_ ?_ h1 h2)
    · refine add_det_nonneg_quad c1 c3 hp ?_ ?_ ?_ ?_ <;>
        simp only [det, alYlo, alR, alN3, alYhi, inPt_fst, inPt_snd] <;> linarith
    · have sw : ∀ x, det ((G + 527, -1) : Point) (inPt (G + 210) vy) x =
          -det (inPt (G + 210) vy) (G + 527, -1) x := fun x => det_swap12 _ _ x
      have := add_det_nonneg_quad (A := ((G + 527, -1) : Point)) (B := inPt (G + 210) vy) c1 c3 hp
        (by simp only [det, alYlo, inPt_fst, inPt_snd]; linarith)
        (by simp only [det, alR, inPt_fst, inPt_snd]; linarith)
        (by simp only [det, alN3, inPt_fst, inPt_snd]; linarith)
        (by simp only [det, alYhi, inPt_fst, inPt_snd]; linarith)
      rw [sw] at this; linarith

/-- **`addLe`, z-pocket (chords argument).**  With the aux guard at `I(v_x, v_y)`, the z-input
at `v_z` and `v_x + v_y ≤ v_z`, every point of the z-pocket is seen by one of them. -/
theorem al_pocketZ_cover (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (alWL G) (alWR G) ⊆ A) (hRP : piece (alRoom G) ⊆ P.filled)
    (hZP : piece (alPocketZ G) ⊆ P.filled) {vx vy vz : ℝ} (hx1 : 1 / 2 ≤ vx) (hy1 : 1 / 2 ≤ vy)
    (hz2 : vz ≤ 2) (hzA : inPt (G + 530) vz ∈ A) (hrel : vx + vy ≤ vz) :
    ∀ p ∈ piece (alPocketZ G), P.Sees (alI G vx vy) p ∨ P.Sees (inPt (G + 530) vz) p := by
  intro p hp
  obtain ⟨c1, c2, c3, c4⟩ := alPocketZ_ccw (G := G)
  have hxy : vx + vy ≤ 2 := by linarith
  have hx2 : vx ≤ 2 := by linarith
  have hy2 : vy ≤ 2 := by linarith
  have hz1 : 1 / 2 ≤ vz := by linarith
  have hy0 : (0 : ℝ) ≤ vy := by linarith
  have hIf := alI_fst (G := G) hx2 hy0
  have hI := alI_mem_auxRegion (G := G) hx1 hy1 hxy
  obtain ⟨q0, q1, q2, q3⟩ := mem_piece_quad.1 hp
  simp only [det, alZlo, alN2, alQ, alZhi] at q0 q1 q2 q3
  have hpd : p.1 ≤ G + 50 := by nlinarith
  have hpl : p.1 = G + 50 → -2994 / 25 ≤ p.2 ∧ p.2 ≤ -118 := fun h => by
    rw [h] at q0 q2; constructor <;> linarith
  have hp2 : p.2 < -1 := by nlinarith
  have hmR : ∀ q : Point, q.1 = G + 50 → -2994 / 25 ≤ q.2 → q.2 ≤ -118 → q ∈ piece (alRoom G) :=
    fun q h1 h2 h3 => alRoom_left h1 (by linarith) (by linarith)
  have hmC : segment ((G + 50, -2994 / 25) : Point) (G + 50, -118) ⊆ piece (alPocketZ G) :=
    add_mouth_subset c1 c2 c3 c4
  have hS := al_shadows_mem hz1 hz2
  have hN2 := alI_N2 (G := G) hx1 hx2 hy1 hy2
  have hQin := al_input_z_Q (G := G) (v := vz) hz2
  have hIQ := alI_Q (G := G) hx2 hy0
  have hrel' := (alI_Q_ge_iff (G := G) (vz := vz) hx2 hy0).2 hrel
  have hgN : (alN2 G).1 < (inPt (G + 530) vz).1 := by simp only [alN2, inPt_fst]; linarith
  have hlh : (alZlo G).2 < (alZhi G).2 := by simp only [alZlo, alZhi]; norm_num
  have hc : G + 30 < (alN2 G).1 := by simp only [alN2]; linarith
  have hs1 : (alZlo G).2 ≤ vproj (inPt (G + 530) vz) (alN2 G) (G + 30) := by
    rw [al_shadow_z]; exact hS.2.2.1.le
  have ha_lo : 0 ≤ det (inPt (G + 530) vz) (alQ G) (alZlo G) :=
    add_det_vert_nonneg (c := G + 30) (h := -2001 / 16) hgN (by linarith)
  have ha_dn : 0 ≤ det (inPt (G + 530) vz) (alQ G) (alN2 G) := by
    simp only [det, alQ, alN2, inPt_fst, inPt_snd]; nlinarith
  have ha_hi : 0 ≤ det (inPt (G + 530) vz) (alQ G) (alZhi G) :=
    add_det_vert_nonneg (c := G + 30) (h := -499 / 4) hgN (by linarith)
  have hb_lo : det (alI G vx vy) (alN2 G) (alZlo G) ≤ 0 :=
    add_det_vert_nonpos (c := G + 30) (h := -2001 / 16) hIf (by linarith)
  have hb_up : det (alI G vx vy) (alN2 G) (alQ G) ≤ 0 := by
    simp only [det, alN2, alQ]; nlinarith
  have hb_hi : det (alI G vx vy) (alN2 G) (alZhi G) ≤ 0 :=
    add_det_vert_nonpos (c := G + 30) (h := -499 / 4) hIf (by linarith)
  have hb_lo' : 0 ≤ det (alI G vx vy) (alQ G) (alZlo G) :=
    add_det_vert_nonneg (c := G + 30) (h := -2001 / 16) hIf
      (by rw [hIQ]; unfold alSx alSy; linarith)
  have hb_dn' : 0 ≤ det (alI G vx vy) (alQ G) (alN2 G) := by
    simp only [det, alQ, alN2]; nlinarith
  have hb_s : 0 ≤ det (alI G vx vy) (alQ G) (G + 30, vproj (inPt (G + 530) vz) (alN2 G) (G + 30)) :=
    add_det_vert_nonneg hIf (by rw [al_shadow_z]; exact hrel')
  rcases add_pocket_split (lo := alZlo G) (dn := alN2 G) (up := alQ G) (hi := alZhi G)
      (ga := inPt (G + 530) vz) (gb := alI G vx vy) (c := G + 30) c1 c3 c4 rfl rfl hlh hc hgN hs1
      ha_lo ha_dn ha_hi hb_lo hb_up hb_hi hb_lo' hb_dn' hb_s hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inr (add_sees_window_vmouth hA hAP (convex_piece _) hRP (convex_piece _) hZP
      (by linarith) (al_window_mem hWA) (by norm_num) (by norm_num) hmR hmC hzA
      (by simp only [inPt_snd]; linarith) hgN hp hpd hpl hp2 ?_ ?_ h1 h2)
    · refine add_det_nonneg_quad c1 c3 hp ?_ ?_ ?_ ?_ <;>
        simp only [det, alZlo, alN2, alQ, alZhi, inPt_fst, inPt_snd] <;> linarith
    · have sw : ∀ x, det ((G + 527, -1) : Point) (inPt (G + 530) vz) x =
          -det (inPt (G + 530) vz) (G + 527, -1) x := fun x => det_swap12 _ _ x
      have := add_det_nonneg_quad (A := ((G + 527, -1) : Point)) (B := inPt (G + 530) vz) c1 c3 hp
        (by simp only [det, alZlo, inPt_fst, inPt_snd]; linarith)
        (by simp only [det, alN2, inPt_fst, inPt_snd]; linarith)
        (by simp only [det, alQ, inPt_fst, inPt_snd]; linarith)
        (by simp only [det, alZhi, inPt_fst, inPt_snd]; linarith)
      rw [sw] at this; linarith
  · exact Or.inl (add_sees_vmouth (convex_piece _) hRP (convex_piece _) hZP (by norm_num) hmR hmC
      hI.2 hIf hp hpd hpl h1 h2)

/-- **`addLe`: the aux guard sees the room** (any point of the room, e.g. of the aux region). -/
theorem al_aux_sees_room (hRP : piece (alRoom G) ⊆ P.filled) {g : Point}
    (hg : g ∈ piece (alRoom G)) : ∀ x ∈ piece (alRoom G), P.Sees g x :=
  fun _ hx => sees_of_convex (convex_piece _) hRP hg hx

/-- **`addLe`: the aux guard sees the aux wedge** (any point of the aux region strictly above
the bottom of the room, e.g. the canonical point). -/
theorem al_aux_sees_auxTri (hRP : piece (alRoom G) ⊆ P.filled)
    (hTP : piece (alAuxTri G) ⊆ P.filled) {g : Point} (hg : g ∈ alAuxRegion G)
    (hg2 : -128 < g.2) : ∀ x ∈ piece (alAuxTri G), P.Sees g x := by
  intro x hx
  obtain ⟨⟨k1, k2⟩, hgR⟩ := hg
  have htri : 0 < det (alM1 G) (alTip G) (alM2 G) := by
    simp only [det, alM1, alTip, alM2]; linarith
  refine add_sees_tri_through htri (convex_piece _) hRP hTP hgR ?_ ?_ ?_ ?_ hx
  · intro q hq
    rw [segment_comm] at hq
    obtain ⟨h1, h2, h3⟩ :=
      (mem_segment_horiz_iff (c := -128) (x₁ := G + 439 / 4) (x₂ := G + 441 / 4) (by linarith)).1 hq
    exact mem_alRoom.2 ⟨by rw [h1]; linarith, by linarith, by linarith, by linarith,
      by linarith⟩
  · simp only [det, alM2, alM1]; nlinarith
  · have e : det g (alM2 G) (alTip G) = -det (alTip G) (alM2 G) g := by unfold det; ring
    rw [e]; linarith
  · have e : det g (alM1 G) (alTip G) = det (alM1 G) (alTip G) g := by unfold det; ring
    rw [e]; exact k1

/-- `addLe`: the needle of the x-input hanging from the bottom of the room. -/
noncomputable def alNeedleX (G H : ℝ) : Polygon :=
  tri (G + 370, -128) (G + 370, -128 - H) (G + 1481 / 4, -128)

/-- `addLe`: the needle of the y-input hanging from the bottom of the room. -/
noncomputable def alNeedleY (G H : ℝ) : Polygon :=
  tri (G + 210, -128) (G + 210, -128 - H) (G + 841 / 4, -128)

/-- An input standing above the window sees its needle hanging from the bottom of the room
(generic form for `addLe`, needle at abscissa `G + δ`, `200 ≤ δ ≤ 1052/2`). -/
theorem al_needle_seen {δ δ' H : ℝ} (hδ1 : 200 ≤ δ) (hδ2 : δ ≤ 526) (hδ' : δ' = δ + 1 / 4)
    (hH : 0 < H)
    (hA : Convex ℝ A) (hAP : A ⊆ P.filled) (hWA : segment (alWL G) (alWR G) ⊆ A)
    (hRP : piece (alRoom G) ⊆ P.filled)
    (hTP : piece (tri (G + δ, -128) (G + δ, -128 - H) (G + δ', -128)) ⊆ P.filled)
    {v : ℝ} (hv1 : 1 / 2 ≤ v) (_hv2 : v ≤ 2) (hgA : inPt (G + δ) v ∈ A) :
    ∀ x ∈ piece (tri (G + δ, -128) (G + δ, -128 - H) (G + δ', -128)),
      P.Sees (inPt (G + δ) v) x := by
  subst hδ'
  intro x hx
  set g := inPt (G + δ) v with hg
  have htri : 0 < det ((G + δ, -128) : Point) (G + δ, -128 - H) (G + (δ + 1 / 4), -128) := by
    simp only [det]; linarith
  obtain ⟨t0, t1, t2⟩ := mem_piece_tri.1 hx
  simp only [det] at t0 t1 t2
  have hx2 : x.2 ≤ -128 := by nlinarith
  have hx1 : G + δ ≤ x.1 := by nlinarith
  have hx1' : x.1 ≤ G + δ + 1 / 4 := by
    by_contra hc; push Not at hc; nlinarith [mul_pos hH (by linarith : (0 : ℝ) < x.1 - G - δ - 1 / 4)]
  have hw1 : 0 ≤ det g (G + 200, -1) x := by
    refine add_det_nonneg_tri htri hx ?_ ?_ ?_ <;> simp only [det, hg, inPt_fst, inPt_snd] <;>
      nlinarith
  have hw2 : det g (G + 527, -1) x ≤ 0 := by
    have sw : ∀ y, det ((G + 527, -1) : Point) g y = -det g (G + 527, -1) y :=
      fun y => det_swap12 _ _ y
    have := add_det_nonneg_tri (A := ((G + 527, -1) : Point)) (B := g) htri hx
      (by rw [sw]; simp only [det, hg, inPt_fst, inPt_snd]; nlinarith)
      (by rw [sw]; simp only [det, hg, inPt_fst, inPt_snd]; nlinarith)
      (by rw [sw]; simp only [det, hg, inPt_fst, inPt_snd]; nlinarith)
    rw [sw] at this; linarith
  obtain ⟨q, hq, e1, e2, e3⟩ := add_cross_window (by linarith) (by simp only [hg, inPt_snd]; linarith)
    (by linarith) hw1 hw2
  obtain ⟨hqA, hqR⟩ := al_window_mem hWA q e1 e2 e3
  have hq1 : G + δ ≤ q.1 ∧ q.1 ≤ G + δ + 1 / 4 := by
    obtain ⟨l, hl0, hl1, rfl⟩ := mem_segment_iff_lerp.1 hq
    simp only [lerp_fst, hg, inPt_fst]
    constructor <;> nlinarith
  refine sees_of_mem_segment hq (sees_of_convex hA hAP hgA hqA) ?_
  refine add_sees_tri_through htri (convex_piece _) hRP hTP hqR ?_ ?_ ?_ ?_ hx
  · intro y hy
    rw [segment_comm] at hy
    obtain ⟨h1, h2, h3⟩ :=
      (mem_segment_horiz_iff (c := -128) (x₁ := G + δ) (x₂ := G + (δ + 1 / 4)) (by linarith)).1 hy
    exact mem_alRoom.2 ⟨by rw [h1]; linarith, by linarith, by linarith, by linarith,
      by linarith⟩
  · simp only [det]; rw [e1]; linarith
  · simp only [det]; rw [e1]; nlinarith [mul_nonneg hH.le (by linarith : (0 : ℝ) ≤ G + δ + 1 / 4 - q.1)]
  · simp only [det]; rw [e1]; nlinarith [mul_nonneg hH.le (by linarith : (0 : ℝ) ≤ q.1 - G - δ)]

/-- **`addLe`: the x-input sees its needle.** -/
theorem al_needleX_seen {H : ℝ} (hH : 0 < H) (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (alWL G) (alWR G) ⊆ A) (hRP : piece (alRoom G) ⊆ P.filled)
    (hTP : piece (alNeedleX G H) ⊆ P.filled) {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hgA : inPt (G + 370) v ∈ A) : ∀ x ∈ piece (alNeedleX G H), P.Sees (inPt (G + 370) v) x := by
  exact al_needle_seen (δ := 370) (δ' := 1481 / 4) (by norm_num) (by norm_num) (by norm_num) hH hA
    hAP hWA hRP hTP hv1 hv2 hgA

/-- **`addLe`: the y-input sees its needle.** -/
theorem al_needleY_seen {H : ℝ} (hH : 0 < H) (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hWA : segment (alWL G) (alWR G) ⊆ A) (hRP : piece (alRoom G) ⊆ P.filled)
    (hTP : piece (alNeedleY G H) ⊆ P.filled) {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hgA : inPt (G + 210) v ∈ A) : ∀ x ∈ piece (alNeedleY G H), P.Sees (inPt (G + 210) v) x := by
  exact al_needle_seen (δ := 210) (δ' := 841 / 4) (by norm_num) (by norm_num) (by norm_num) hH hA
    hAP hWA hRP hTP hv1 hv2 hgA

end addLe

end Stade

end ArtGallery

end
