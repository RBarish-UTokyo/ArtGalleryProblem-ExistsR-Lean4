module

public import ArtGallery.Stade.Exit

/-!
# Generic visibility tools for the canonical guard set (proof plan §9)

Elementary facts used to show that the canonical guards of Stade's construction see every point
of the region:

* `aff_nonneg_of_mem_segment`: an affine inequality valid at both ends of a segment holds on the
  segment (used to locate sight lines inside unions of convex pieces);
* `mem_segment_of_side`: a point of the line of a side `a b`, weakly inside the two neighbouring
  sides of a convex corner chain `p, a, b, n`, lies on the side;
* `cross_tri`, `cross_quad`: if `g` is weakly inside all sides of a triangle / quadrilateral
  except the last one (the *door*) and weakly outside the door, the segment from `g` to any point
  of the piece meets the door;
* `fan_tri`, `quad_fan`: every point of a triangle lies on a segment from a vertex to the
  opposite side; every point of a convex quadrilateral lies on a segment joining two opposite
  sides;
* `pasch`: a segment from `g` to a point of the side `s m` of the triangle `g, s, m` meets every
  segment from a point of `g s` to `m`;
* `pocket_cover`: a convex pocket whose nook points are each seen through the mouth by one of
  several guards, each of which sees the whole mouth, is seen entirely by these guards.
-/

@[expose] public section

namespace ArtGallery.Stade

open Set
open ArtGallery.Geometry (lerp det_lerp lerp_mem_segment)

variable {P : Polygon}

/-! ### Affine inequalities along segments -/

/-- An affine inequality `0 ≤ α x + β y + γ` valid at both ends of a segment holds on it. -/
theorem aff_nonneg_of_mem_segment {g z p : Point} (hp : p ∈ segment g z) (α β γ : ℝ)
    (hg : 0 ≤ α * g.1 + β * g.2 + γ) (hz : 0 ≤ α * z.1 + β * z.2 + γ) :
    0 ≤ α * p.1 + β * p.2 + γ := by
  obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hp
  simp only [Geometry.lerp_fst, Geometry.lerp_snd]
  have : α * (g.1 + t * (z.1 - g.1)) + β * (g.2 + t * (z.2 - g.2)) + γ =
      (1 - t) * (α * g.1 + β * g.2 + γ) + t * (α * z.1 + β * z.2 + γ) := by ring
  rw [this]
  exact add_nonneg (mul_nonneg (by linarith) hg) (mul_nonneg ht0 hz)

/-- `det` is nonnegative on a segment when it is at both ends. -/
theorem det_nonneg_of_mem_segment {a b g z p : Point} (hp : p ∈ segment g z)
    (hg : 0 ≤ det a b g) (hz : 0 ≤ det a b z) : 0 ≤ det a b p := by
  obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hp
  rw [det_lerp]
  exact add_nonneg (mul_nonneg (by linarith) hg) (mul_nonneg ht0 hz)

/-! ### Points on a side -/

/-- A point on the line of the side `a b` that is weakly to the left of the neighbouring sides
`p a` and `b n` (strictly convex corners at `a` and `b`) lies on the segment `a b`. -/
theorem mem_segment_of_side {p a b n q : Point} (h1 : 0 < det p a b) (h2 : 0 < det a b n)
    (hq : det a b q = 0) (hp : 0 ≤ det p a q) (hn : 0 ≤ det b n q) : q ∈ segment a b := by
  have hab : a ≠ b := by
    rintro rfl; simp at h2
  obtain ⟨t, rfl⟩ := Geometry.exists_lerp_of_det_eq_zero hab hq
  rw [det_lerp] at hp hn
  simp only [Geometry.det_self_right, Geometry.det_self_outer, mul_zero, zero_add,
    add_zero] at hp hn
  have e : det b n a = det a b n := Geometry.det_cyclic a b n
  rw [e] at hn
  have ht0 : 0 ≤ t := by
    by_contra h; push Not at h; nlinarith
  have ht1 : t ≤ 1 := by
    by_contra h; push Not at h; nlinarith
  exact lerp_mem_segment a b ht0 ht1

/-! ### Crossing the door of a triangle or quadrilateral -/

/-- The point of a segment `g z` on the line `det a b · = 0` when `det a b g ≤ 0 ≤ det a b z`. -/
theorem exists_zero_on_segment {a b g z : Point} (hg : det a b g ≤ 0) (hz : 0 ≤ det a b z) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ det a b (lerp g z t) = 0 := by
  by_cases h : det a b z - det a b g = 0
  · refine ⟨1, zero_le_one, le_rfl, ?_⟩
    rw [Geometry.lerp_one]; linarith
  · have hpos : 0 < det a b z - det a b g := lt_of_le_of_ne (by linarith) (Ne.symm h)
    refine ⟨-det a b g / (det a b z - det a b g), div_nonneg (by linarith) hpos.le,
      (div_le_one hpos).2 (by linarith), ?_⟩
    rw [det_lerp]
    field_simp
    ring

/-- **Crossing the door of a triangle.**  `a b c` counter-clockwise, `g` weakly left of the
sides `a b`, `b c` and weakly right of the door `c a`: every segment from `g` to a point of the
triangle meets the door. -/
theorem cross_tri {a b c g z : Point} (hD : 0 < det a b c) (hg1 : 0 ≤ det a b g)
    (hg2 : 0 ≤ det b c g) (hg3 : det c a g ≤ 0) (hz : z ∈ piece (tri a b c)) :
    ∃ q ∈ segment c a, q ∈ segment g z := by
  obtain ⟨hz1, hz2, hz3⟩ := mem_piece_tri.1 hz
  obtain ⟨t, ht0, ht1, ht⟩ := exists_zero_on_segment hg3 hz3
  have hq := lerp_mem_segment g z ht0 ht1
  refine ⟨lerp g z t, ?_, hq⟩
  have e1 : det b c a = det a b c := Geometry.det_cyclic a b c
  have e2 : det c a b = det a b c := Geometry.det_cyclic_right a b c
  exact mem_segment_of_side (p := b) (n := b) (by rw [e1]; exact hD) (by rw [e2]; exact hD) ht
    (det_nonneg_of_mem_segment hq hg2 hz2) (det_nonneg_of_mem_segment hq hg1 hz1)

/-- **Crossing the door of a quadrilateral.**  `a b c d` strictly convex counter-clockwise,
`g` weakly left of the sides `a b`, `b c`, `c d` and weakly right of the door `d a`: every
segment from `g` to a point of the quadrilateral meets the door. -/
theorem cross_quad {a b c d g z : Point} (hcda : 0 < det c d a) (hdab : 0 < det d a b)
    (hg1 : 0 ≤ det a b g) (hg3 : 0 ≤ det c d g) (hg4 : det d a g ≤ 0)
    (hz : z ∈ piece (quad a b c d)) : ∃ q ∈ segment d a, q ∈ segment g z := by
  obtain ⟨hz1, -, hz3, hz4⟩ := mem_piece_quad.1 hz
  obtain ⟨t, ht0, ht1, ht⟩ := exists_zero_on_segment hg4 hz4
  have hq := lerp_mem_segment g z ht0 ht1
  exact ⟨lerp g z t, mem_segment_of_side hcda hdab ht (det_nonneg_of_mem_segment hq hg3 hz3)
    (det_nonneg_of_mem_segment hq hg1 hz1), hq⟩

/-! ### Fans -/

/-- **Fan of a triangle.** Every point of a counter-clockwise triangle `a b c` lies on a segment
from `a` to a point of the opposite side `b c`. -/
theorem fan_tri {a b c z : Point} (hD : 0 < det a b c) (hz : z ∈ piece (tri a b c)) :
    ∃ m ∈ segment b c, z ∈ segment a m := by
  obtain ⟨hz1, hz2, hz3⟩ := mem_piece_tri.1 hz
  -- the line `a z` meets `b c` at `m`
  have h0 : det a z b ≤ 0 := by rw [Geometry.det_swap23]; linarith
  have h1 : 0 ≤ det a z c := by rw [← Geometry.det_cyclic_right]; exact hz3
  obtain ⟨τ, hτ0, hτ1, hτ⟩ := exists_zero_on_segment h0 h1
  set m := lerp b c τ with hm
  refine ⟨m, lerp_mem_segment b c hτ0 hτ1, ?_⟩
  have habm : det a b m = τ * det a b c := by
    rw [hm, det_lerp]; simp
  have hcam : det c a m = (1 - τ) * det a b c := by
    rw [hm, det_lerp, Geometry.det_cyclic_right]; simp
  have hbcm : det b c m = 0 := by rw [hm]; exact Geometry.det_lerp_self b c τ
  have ham : a ≠ m := by
    intro h
    have : det b c a = 0 := by rw [h]; exact hbcm
    rw [Geometry.det_cyclic] at this; linarith
  have hzline : det a m z = 0 := by
    have : det a z m = 0 := hτ
    rw [Geometry.det_swap23] at this; linarith
  obtain ⟨lam, rfl⟩ := Geometry.exists_lerp_of_det_eq_zero ham hzline
  have e1 : det b c (lerp a m lam) = (1 - lam) * det a b c := by
    rw [det_lerp, hbcm, Geometry.det_cyclic]; ring
  have e2 : det a b (lerp a m lam) + det c a (lerp a m lam) = lam * det a b c := by
    have q1 := det_lerp a b a m lam
    have q2 := det_lerp c a a m lam
    simp only [Geometry.det_self_outer, Geometry.det_self_right, mul_zero, zero_add] at q1 q2
    rw [q1, q2, habm, hcam]; ring
  have hl1 : lam ≤ 1 := by
    by_contra h; push Not at h; nlinarith
  have hl0 : 0 ≤ lam := by
    by_contra h; push Not at h; nlinarith
  exact lerp_mem_segment a m hl0 hl1

/-- **Fan of a quadrilateral.**  Every point of a strictly convex counter-clockwise
quadrilateral `lo dn up hi` lies on a segment from a point of the side `lo hi` to a point of the
opposite side `dn up`. -/
theorem quad_fan {lo dn up hi z : Point} (h1 : 0 < det lo dn up) (_h2 : 0 < det dn up hi)
    (h3 : 0 < det up hi lo) (_h4 : 0 < det hi lo dn) (hz : z ∈ piece (quad lo dn up hi)) :
    ∃ s ∈ segment lo hi, ∃ m ∈ segment dn up, z ∈ segment s m := by
  obtain ⟨hz1, hz2, hz3, hz4⟩ := mem_piece_quad.1 hz
  by_cases hc : 0 ≤ det lo up z
  · -- `z` in the triangle `up hi lo`: fan from `up`
    have hD : 0 < det up hi lo := h3
    have hzt : z ∈ piece (tri up hi lo) := by
      exact mem_piece_tri.2 ⟨hz3, hz4, hc⟩
    obtain ⟨s, hs, hzs⟩ := fan_tri hD hzt
    refine ⟨s, by rw [Geometry.segment_comm]; exact hs, up, Geometry.right_mem_segment dn up, ?_⟩
    rw [Geometry.segment_comm]; exact hzs
  · push Not at hc
    have hD : 0 < det lo dn up := h1
    have hzt : z ∈ piece (tri lo dn up) := by
      refine mem_piece_tri.2 ⟨hz1, hz2, ?_⟩
      have : det up lo z = - det lo up z := Geometry.det_swap12 lo up z
      linarith
    obtain ⟨m, hm, hzm⟩ := fan_tri hD hzt
    exact ⟨lo, Geometry.left_mem_segment lo hi, m, hm, hzm⟩

/-! ### Pasch -/

/-- **Pasch.**  If `q₁` lies on `g s` and `z` on `s m`, then the segment `g z` meets the segment
`q₁ m`. -/
theorem pasch {g s m q₁ z : Point} (hq₁ : q₁ ∈ segment g s) (hz : z ∈ segment s m) :
    ∃ q ∈ segment q₁ m, q ∈ segment g z := by
  obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hq₁
  obtain ⟨l, hl0, hl1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hz
  -- the point `β`-th of the way from `g` to `z`, `β = t / (1 - l + l t)`
  have hden : 0 < 1 - l + l * t ∨ (l = 1 ∧ t = 0) := by
    by_cases h : l = 1 ∧ t = 0
    · exact Or.inr h
    · left
      rcases not_and_or.1 h with h | h
      · have : l < 1 := lt_of_le_of_ne hl1 h
        nlinarith
      · have : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h)
        nlinarith
  rcases hden with hden | ⟨rfl, rfl⟩
  · obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = t / (1 - l + l * t) := ⟨_, rfl⟩
    have hβ0 : 0 ≤ β := hβ ▸ div_nonneg ht0 hden.le
    have hβ1 : β ≤ 1 := hβ ▸ (div_le_one hden).2 (by nlinarith)
    have hβl : β * l ≤ 1 := by nlinarith
    refine ⟨lerp g (lerp s m l) β, ?_, lerp_mem_segment _ _ hβ0 hβ1⟩
    refine Geometry.mem_segment_iff_lerp.2 ⟨β * l, by positivity, hβl, ?_⟩
    have key : β * (1 - l + l * t) = t := by rw [hβ, div_mul_cancel₀]; exact hden.ne'
    ext
    · simp only [Geometry.lerp_fst]; linear_combination (s.1 - g.1) * key
    · simp only [Geometry.lerp_snd]; linear_combination (s.2 - g.2) * key
  · refine ⟨m, Geometry.right_mem_segment _ _, ?_⟩
    simp only [Geometry.lerp_one]
    exact Geometry.right_mem_segment _ _

/-- Rotating the vertex list of a quadrilateral does not change its piece. -/
theorem piece_quad_rot (a b c d : Point) : piece (quad a b c d) = piece (quad b c d a) := by
  ext x; simp only [mem_piece_quad]; tauto

/-- Rotating the vertex list of a triangle does not change its piece. -/
theorem piece_tri_rot (a b c : Point) : piece (tri a b c) = piece (tri b c a) := by
  ext x; simp only [mem_piece_tri]; tauto

/-! ### Sight lines -/

/-- If the segment `g z` passes through a point `q` seen by `g`, and `q`, `z` lie in a convex
part of the region, then `g` sees `z`. -/
theorem sees_via {C : Set Point} (hC : Convex ℝ C) (hCP : C ⊆ P.filled) {g z q : Point}
    (hq : q ∈ segment g z) (hgq : P.Sees g q) (hqC : q ∈ C) (hzC : z ∈ C) : P.Sees g z :=
  sees_of_mem_segment hq hgq (sees_of_convex hC hCP hqC hzC)

/-- **Pocket coverage.**  Let `K = lo dn up hi` be a strictly convex counter-clockwise
quadrilateral in the region, with *nook* side `lo hi` and *mouth* `dn up`.  If every guard of
`Gs` sees every point of the mouth and every nook point is seen *through the mouth* by some guard
of `Gs`, then every point of `K` is seen by some guard of `Gs`. -/
theorem pocket_cover {lo dn up hi : Point} (h1 : 0 < det lo dn up) (h2 : 0 < det dn up hi)
    (h3 : 0 < det up hi lo) (h4 : 0 < det hi lo dn) (hKP : piece (quad lo dn up hi) ⊆ P.filled)
    {Gs : Set Point} (hmouth : ∀ g ∈ Gs, ∀ m ∈ segment dn up, P.Sees g m)
    (hnook : ∀ s ∈ segment lo hi, ∃ g ∈ Gs, ∃ q ∈ segment dn up, q ∈ segment g s) :
    ∀ z ∈ piece (quad lo dn up hi), ∃ g ∈ Gs, P.Sees g z := by
  intro z hz
  obtain ⟨s, hs, m, hm, hzsm⟩ := quad_fan h1 h2 h3 h4 hz
  obtain ⟨g, hg, q₁, hq₁, hq₁s⟩ := hnook s hs
  obtain ⟨q, hq, hqz⟩ := pasch hq₁s hzsm
  have hqm : q ∈ segment dn up := by
    have hc : Convex ℝ (segment dn up) := by rw [Geometry.segment_eq]; exact convex_segment _ _
    exact Geometry.segment_subset_of_convex hc hq₁ hm hq
  have hmK : segment dn up ⊆ piece (quad lo dn up hi) := by
    have hK : IsPiece (quad lo dn up hi) := isPiece_quad h1 h2 h3 h4
    have := edge_subset_piece hK (j := 1) (by simp [quad_n])
    rwa [(quad_edge lo dn up hi).2.1] at this
  exact ⟨g, hg, sees_via (convex_piece _) hKP hqz (hmouth g hg q hqm) (hmK hqm) hz⟩

end ArtGallery.Stade

end
