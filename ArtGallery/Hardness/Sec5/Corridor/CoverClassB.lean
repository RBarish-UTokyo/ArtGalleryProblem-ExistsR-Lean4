module

public import ArtGallery.Hardness.Sec5.Corridor.CoverClassA

/-!
# Section 5: corridors — locating the interior points of the corridor above the floor

`Good.classify_upper`: an interior point `z` of the corridor on or above the floor line, not on
the vertical lines through the stationary guards, lies in the strip piece, the umbra piece or the
nook piece (strictly above the mouth) of some pair `k`.  The pair is given by the strip containing
`z.x`; the upper-wall point `w` directly above `z` lies on one of the six edges of pair `k`
(`Good.mid_edge`), and each edge gives the position of `z`.
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ}

/-- The classification of a point of the corridor (pair `k`). -/
def Classified (I : Input) (k : ℕ) (z : Point) : Prop :=
  z ∈ hpSet (I.stripFs k) ∨ z ∈ hpSet (I.umbraFs k) ∨
    (z ∈ hpSet (I.nookFs k) ∧ I.lYR (ratPoint (I.z1 k)) < I.lYR z)

/-- `det` at a point below another one. -/
theorem det_below (a b w z : Point) (hx : w.1 = z.1) :
    ArtGallery.det a b z = ArtGallery.det a b w - (b.1 - a.1) * (z.2 - w.2) * (-1) := by
  simp only [ArtGallery.det, hx]; ring

/-- `det` vanishes on the segment. -/
theorem det_seg {a b w : Point} (hw : w ∈ ArtGallery.segment a b) : ArtGallery.det a b w = 0 := by
  obtain ⟨t, -, -, rfl⟩ := hw
  simp only [ArtGallery.det]; ring

/-- The common situation: `z` interior to the strip of `k`, `w` directly above `z` on an
upper-wall edge. -/
structure Above (I : Input) (k : ℕ) (z w : Point) : Prop where
  hx : w.1 = z.1
  hy : z.2 < w.2
  h1 : I.lXR (ratPoint (I.nxt k)) < I.lXR z
  h2 : I.lXR z < I.lXR (ratPoint (I.sgPt k))
  hH : -(8 * (I.S : ℝ)) ≤ I.lYR z

theorem Above.lx {k : ℕ} {z w : Point} (h : Above I k z w) : I.lXR w = I.lXR z := by
  simp only [lXR, h.hx]

theorem Above.ly {k : ℕ} {z w : Point} (h : Above I k z w) (hS : (0 : ℝ) < I.S) : I.lYR z < I.lYR w := by
  simp only [lYR]; have := h.hy; nlinarith

section Classify

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

omit hg hk in
/-- The umbra-or-strip alternative below the mouth, given the edge and wall conditions. -/
theorem Good.umbra_or_strip (_hg : I.Good N) {z : Point} (_hk : k < I.np)
    (h1 : I.lXR (ratPoint (I.nxt k)) < I.lXR z) (h2 : I.lXR z < I.lXR (ratPoint (I.sgPt k)))
    (hH : -(8 * (I.S : ℝ)) ≤ I.lYR z)
    (hE : 0 ≤ ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)) z)
    (hY : I.lYR z ≤ I.lYR (ratPoint (I.z1 k)))
    (hW : 0 ≤ ArtGallery.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) z)
    (hX : I.lXR z ≤ I.lXR (ratPoint (I.zp k))) : I.Classified k z := by
  rcases le_or_gt 0 (I.AR k z) with hA | hA
  · right; left
    rw [mem_umbra_iff]; exact ⟨hA, hE, hY, hW, hX, h1.le, hH⟩
  · left
    rw [mem_strip_iff]; exact ⟨h2.le, h1.le, hH, hA.le, hW⟩

/-- Coordinates of the six vertices. -/
theorem Good.six_coords :
    I.lXR (ratPoint (I.zp k)) < I.lXR (ratPoint (I.sgPt k)) ∧
    I.lXR (ratPoint (I.z1 k)) < I.lXR (ratPoint (I.zp k)) ∧
    I.lYR (ratPoint (I.zp k)) < I.lYR (ratPoint (I.z1 k)) ∧
    I.lXR (ratPoint (I.n1 k)) = I.lXR (ratPoint (I.z1 k)) ∧
    I.lYR (ratPoint (I.z1 k)) < I.lYR (ratPoint (I.n1 k)) ∧
    I.lXR (ratPoint (I.n0 k)) = I.lXR (ratPoint (I.z0 k)) ∧
    I.lYR (ratPoint (I.z1 k)) < I.lYR (ratPoint (I.n0 k)) ∧
    I.lXR (ratPoint (I.z0 k)) < I.lXR (ratPoint (I.z1 k)) ∧
    I.lYR (ratPoint (I.z0 k)) = I.lYR (ratPoint (I.z1 k)) ∧
    I.lXR (ratPoint (I.nxt k)) < I.lXR (ratPoint (I.z0 k)) ∧
    I.lYR (ratPoint (I.nxt k)) < I.lYR (ratPoint (I.z0 k)) := by
  obtain ⟨zx, zy, -, -, -⟩ := hg.rl_zp hk
  obtain ⟨z1x, z1y⟩ := hg.rl_z1 hk
  obtain ⟨z0x, z0y⟩ := hg.rl_z0 hk
  obtain ⟨n1x, n1y⟩ := hg.rl_n1 hk
  obtain ⟨n0x, n0y⟩ := hg.rl_n0 hk
  obtain ⟨nn1, nn2⟩ := hg.rl_nxt hk
  obtain ⟨-, -, hS1, -⟩ := hg.S_big
  obtain ⟨l1, l2, r1, r2, hN, -, hw⟩ := hg.pairR hk
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at zx zy n1y n0y hw2
  have hpz := hg.sg_east_zp hk
  have hnxt : I.lXR (ratPoint (I.nxt k)) < I.lXR (ratPoint (I.z0 k)) ∧
      I.lYR (ratPoint (I.nxt k)) < I.lYR (ratPoint (I.z0 k)) := by
    rw [z0x, z0y]
    by_cases h : k + 1 < I.np
    · rw [(nn1 h).1, (nn1 h).2]; constructor <;> linarith
    · rw [(nn2 h).1, (nn2 h).2]; constructor <;> nlinarith
  refine ⟨by linarith, by rw [z1x]; linarith, by rw [z1y]; linarith, by rw [n1x, z1x],
    by rw [z1y]; linarith, by rw [n0x, z0x], by rw [z1y]; linarith, by rw [z0x, z1x]; linarith,
    by rw [z0y, z1y], hnxt.1, hnxt.2⟩

/-- Case `p_k → z'_k`. -/
theorem Good.class_axis {z w : Point} (h : Above I k z w)
    (hw : w ∈ ArtGallery.segment (ratPoint (I.sgPt k)) (ratPoint (I.zp k))) :
    I.Classified k z := by
  obtain ⟨c1, -⟩ := hg.six_coords hk
  obtain ⟨-, -, -, -, hSp, -⟩ := hg.S_big
  obtain ⟨hD1, -⟩ := hg.DDR_bounds hk
  have hAw : I.AR k w = 0 := by
    have hz0 := (hg.rl_zp hk).2.2.2.2
    have hp0 := hg.AR_sgPt hk
    have a := (I.cA (-((I.hh k : ℚ) : ℝ)) ((I.DD k : ℚ) : ℝ)
      (-(8 * I.S * ((I.gg k : ℚ) : ℝ)))).ev_le_of_segment hw (c := 0)
      (by rw [← AR_eq_cA, hp0]) (by rw [← AR_eq_cA, hz0])
    have b := (I.cA (-((I.hh k : ℚ) : ℝ)) ((I.DD k : ℚ) : ℝ)
      (-(8 * I.S * ((I.gg k : ℚ) : ℝ)))).ge_ev_of_segment hw (c := 0)
      (by rw [← AR_eq_cA, hp0]) (by rw [← AR_eq_cA, hz0])
    rw [← AR_eq_cA] at a b; linarith
  have hAz : I.AR k z < 0 := by
    have hly := h.ly hSp
    have : I.AR k z = I.AR k w - ((I.DD k : ℚ) : ℝ) * (I.lYR w - I.lYR z) := by
      simp only [AR]; rw [h.lx]; ring
    rw [this, hAw]; nlinarith
  have hxw : I.lXR (ratPoint (I.zp k)) ≤ I.lXR w := by
    have := (I.cA 1 0 0).ge_ev_of_segment hw (c := I.lXR (ratPoint (I.zp k)))
      (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
    rw [ev_cA] at this; linarith
  rw [h.lx] at hxw
  left
  rw [mem_strip_iff]
  exact ⟨h.h2.le, h.h1.le, h.hH, hAz.le, hg.wall_below_axis hk hxw hAz.le⟩

/-- Case `z'_k → z1`. -/
theorem Good.class_edge {z w : Point} (h : Above I k z w)
    (hw : w ∈ ArtGallery.segment (ratPoint (I.zp k)) (ratPoint (I.z1 k))) :
    I.Classified k z := by
  obtain ⟨c1, c2, c3, -, -, -, -, c8, c9, -, -⟩ := hg.six_coords hk
  obtain ⟨-, -, -, -, hSp, h64⟩ := hg.S_big
  have hly := h.ly hSp
  have hE : 0 ≤ ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)) z := by
    rw [det_below _ _ w z h.hx, det_seg hw]
    have hx : (ratPoint (I.z1 k)).1 - (ratPoint (I.zp k)).1 < 0 := by
      have := (lXR_lt_iff' hg).1 c2; linarith
    have hy : z.2 - w.2 < 0 := by linarith [h.hy]
    nlinarith
  have hyw : I.lYR w ≤ I.lYR (ratPoint (I.z1 k)) := by
    have := (I.cA 0 1 0).ev_le_of_segment hw (c := I.lYR (ratPoint (I.z1 k)))
      (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
    rw [ev_cA] at this; linarith
  have hxw : I.lXR (ratPoint (I.z1 k)) ≤ I.lXR w ∧ I.lXR w ≤ I.lXR (ratPoint (I.zp k)) := by
    have a := (I.cA 1 0 0).ge_ev_of_segment hw (c := I.lXR (ratPoint (I.z1 k)))
      (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
    have b := (I.cA 1 0 0).ev_le_of_segment hw (c := I.lXR (ratPoint (I.zp k)))
      (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
    rw [ev_cA] at a b; constructor <;> linarith
  rw [h.lx] at hxw
  exact hg.umbra_or_strip hk h.h1 h.h2 h.hH hE (by linarith)
    (hg.wall_quadrant hk (by linarith) (by rw [c9]; linarith)) hxw.2

/-- Below the mouth, between the vertical lines through `z0` and `z1`. -/
theorem Good.class_low {z : Point} (h1 : I.lXR (ratPoint (I.nxt k)) < I.lXR z)
    (h2 : I.lXR z < I.lXR (ratPoint (I.sgPt k))) (hH : -(8 * (I.S : ℝ)) ≤ I.lYR z)
    (hx0 : I.lXR (ratPoint (I.z0 k)) ≤ I.lXR z) (hx1 : I.lXR z ≤ I.lXR (ratPoint (I.z1 k)))
    (hy : I.lYR z ≤ I.lYR (ratPoint (I.z1 k))) : I.Classified k z := by
  obtain ⟨c1, c2, c3, -, -, -, -, c8, c9, -, -⟩ := hg.six_coords hk
  exact hg.umbra_or_strip hk h1 h2 hH (hg.edge_quadrant hk hx1 hy) hy
    (hg.wall_quadrant hk hx0 (by rw [c9]; exact hy)) (by linarith)

/-- Case `z1 → n1` (vertical). -/
theorem Good.class_z1n1 {z w : Point} (h : Above I k z w)
    (hw : w ∈ ArtGallery.segment (ratPoint (I.z1 k)) (ratPoint (I.n1 k))) :
    I.Classified k z := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, -, -⟩ := hg.six_coords hk
  obtain ⟨-, -, -, -, hSp, h64⟩ := hg.S_big
  have hly := h.ly hSp
  have hxw : I.lXR w = I.lXR (ratPoint (I.z1 k)) := by
    have a := (I.cA 1 0 0).ge_ev_of_segment hw (c := I.lXR (ratPoint (I.z1 k)))
      (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
    have b := (I.cA 1 0 0).ev_le_of_segment hw (c := I.lXR (ratPoint (I.z1 k)))
      (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
    rw [ev_cA] at a b; linarith
  have hyw : I.lYR w ≤ I.lYR (ratPoint (I.n1 k)) := by
    have := (I.cA 0 1 0).ev_le_of_segment hw (c := I.lYR (ratPoint (I.n1 k)))
      (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
    rw [ev_cA] at this; linarith
  rw [h.lx] at hxw
  rcases le_or_gt (I.lYR z) (I.lYR (ratPoint (I.z1 k))) with hy | hy
  · exact hg.class_low hk h.h1 h.h2 h.hH (by linarith) hxw.le hy
  · right; right
    refine ⟨?_, hy⟩
    rw [mem_nook_iff]
    refine ⟨by linarith, hxw.le, hy.le, ?_⟩
    refine nonneg_of_mul_nonneg_c h64 ?_
    rw [det_lXR, c4, ← hxw, c6]
    have : I.lXR (ratPoint (I.z0 k)) - I.lXR (ratPoint (I.z1 k)) < 0 := by linarith
    nlinarith

/-- Case `n1 → n0` (the nook top edge). -/
theorem Good.class_top {z w : Point} (h : Above I k z w)
    (hw : w ∈ ArtGallery.segment (ratPoint (I.n1 k)) (ratPoint (I.n0 k))) :
    I.Classified k z := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, -, -⟩ := hg.six_coords hk
  obtain ⟨-, -, -, -, hSp, h64⟩ := hg.S_big
  have hxw : I.lXR (ratPoint (I.z0 k)) ≤ I.lXR w ∧ I.lXR w ≤ I.lXR (ratPoint (I.z1 k)) := by
    have a := (I.cA 1 0 0).ge_ev_of_segment hw (c := I.lXR (ratPoint (I.z0 k)))
      (by rw [ev_cA, c4]; linarith) (by rw [ev_cA, c6]; linarith)
    have b := (I.cA 1 0 0).ev_le_of_segment hw (c := I.lXR (ratPoint (I.z1 k)))
      (by rw [ev_cA, c4]; linarith) (by rw [ev_cA, c6]; linarith)
    rw [ev_cA] at a b; constructor <;> linarith
  rw [h.lx] at hxw
  rcases le_or_gt (I.lYR z) (I.lYR (ratPoint (I.z1 k))) with hy | hy
  · exact hg.class_low hk h.h1 h.h2 h.hH hxw.1 hxw.2 hy
  · right; right
    refine ⟨?_, hy⟩
    rw [mem_nook_iff]
    refine ⟨hxw.1, hxw.2, hy.le, ?_⟩
    rw [det_below _ _ w z h.hx, det_seg hw]
    have hx : (ratPoint (I.n0 k)).1 - (ratPoint (I.n1 k)).1 < 0 := by
      have := (lXR_lt_iff' hg).1 (show I.lXR (ratPoint (I.n0 k)) < I.lXR (ratPoint (I.n1 k)) by
        rw [c4, c6]; exact c8)
      linarith
    have hy' : z.2 - w.2 < 0 := by linarith [h.hy]
    nlinarith

/-- Case `n0 → z0` (vertical). -/
theorem Good.class_n0z0 {z w : Point} (h : Above I k z w)
    (hw : w ∈ ArtGallery.segment (ratPoint (I.n0 k)) (ratPoint (I.z0 k))) :
    I.Classified k z := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, -, -⟩ := hg.six_coords hk
  obtain ⟨-, -, -, -, hSp, h64⟩ := hg.S_big
  have hly := h.ly hSp
  have hxw : I.lXR w = I.lXR (ratPoint (I.z0 k)) := by
    have a := (I.cA 1 0 0).ge_ev_of_segment hw (c := I.lXR (ratPoint (I.z0 k)))
      (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
    have b := (I.cA 1 0 0).ev_le_of_segment hw (c := I.lXR (ratPoint (I.z0 k)))
      (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
    rw [ev_cA] at a b; linarith
  have hyw : I.lYR w ≤ I.lYR (ratPoint (I.n0 k)) := by
    have := (I.cA 0 1 0).ev_le_of_segment hw (c := I.lYR (ratPoint (I.n0 k)))
      (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
    rw [ev_cA] at this; linarith
  rw [h.lx] at hxw
  rcases le_or_gt (I.lYR z) (I.lYR (ratPoint (I.z1 k))) with hy | hy
  · exact hg.class_low hk h.h1 h.h2 h.hH hxw.ge (by linarith) hy
  · right; right
    refine ⟨?_, hy⟩
    rw [mem_nook_iff]
    refine ⟨hxw.ge, by linarith, hy.le, ?_⟩
    refine nonneg_of_mul_nonneg_c h64 ?_
    rw [det_lXR, c4, c6, ← hxw]
    have : I.lXR (ratPoint (I.z0 k)) - I.lXR (ratPoint (I.z1 k)) < 0 := by linarith
    nlinarith

/-- Case `z0 → nxt_k` (the left wall). -/
theorem Good.class_wall {z w : Point} (h : Above I k z w)
    (hw : w ∈ ArtGallery.segment (ratPoint (I.z0 k)) (ratPoint (I.nxt k))) :
    I.Classified k z := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := hg.six_coords hk
  obtain ⟨-, -, -, -, hSp, h64⟩ := hg.S_big
  have hly := h.ly hSp
  have hW : 0 ≤ ArtGallery.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) z := by
    rw [det_below _ _ w z h.hx, det_seg hw]
    have hx : (ratPoint (I.nxt k)).1 - (ratPoint (I.z0 k)).1 < 0 := by
      have := (lXR_lt_iff' hg).1 c10; linarith
    have hy : z.2 - w.2 < 0 := by linarith [h.hy]
    nlinarith
  have hyw : I.lYR w ≤ I.lYR (ratPoint (I.z0 k)) := by
    have := (I.cA 0 1 0).ev_le_of_segment hw (c := I.lYR (ratPoint (I.z0 k)))
      (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
    rw [ev_cA] at this; linarith
  have hxw : I.lXR w ≤ I.lXR (ratPoint (I.z0 k)) := by
    have := (I.cA 1 0 0).ev_le_of_segment hw (c := I.lXR (ratPoint (I.z0 k)))
      (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
    rw [ev_cA] at this; linarith
  rw [h.lx] at hxw
  exact hg.umbra_or_strip hk h.h1 h.h2 h.hH
    (hg.edge_quadrant hk (by linarith) (by rw [← c9]; linarith)) (by rw [← c9]; linarith) hW
    (by linarith)

end Classify

section Main

variable (hg : I.Good N)
include hg

/-- **Classification of the interior points above the floor.** -/
theorem Good.classify_upper {z : Point} (hzK : z ∈ I.poly.filled) (hzb : z ∉ I.poly.boundary)
    (hzH : (I.H : ℝ) ≤ z.2) (hzx : ∀ j < I.np, I.lXR z ≠ I.lXR (ratPoint (I.sgPt j))) :
    ∃ k < I.np, I.Classified k z := by
  obtain ⟨hx1, hx2⟩ := hg.interior_x hzK hzb
  obtain ⟨-, -, -, -, hSp, -⟩ := hg.S_big
  have hlx1 : -(8 * (I.S : ℝ)) < I.lXR z := by simp only [lXR]; nlinarith
  have hlx2 : I.lXR z < 8 * (I.S : ℝ) := by simp only [lXR]; nlinarith
  have h0 : 0 < I.np := by have := hg.np_pos; omega
  obtain ⟨k, -, hk, hk1, hk2⟩ := hg.strip_west h0 hlx1.le (by rw [rl_sgPt_zero]; exact hlx2.le)
  have hk2' : I.lXR z < I.lXR (ratPoint (I.sgPt k)) := lt_of_le_of_ne hk2 (hzx k hk)
  have hk1' : I.lXR (ratPoint (I.nxt k)) < I.lXR z := by
    refine lt_of_le_of_ne hk1 ?_
    by_cases h : k + 1 < I.np
    · rw [← hg.sgPt_succ_nxt h]; exact (hzx (k + 1) h).symm
    · rw [((hg.rl_nxt hk).2 h).1]; exact hlx1.ne
  have hH : -(8 * (I.S : ℝ)) ≤ I.lYR z := by simp only [lYR]; nlinarith
  obtain ⟨e, he, w, hwe, hwx, hwy⟩ := hg.upper_point hzK hzb hzH
  have hA : Above I k z w := ⟨hwx, hwy, hk1', hk2', hH⟩
  have hlw : I.lXR w = I.lXR z := hA.lx
  refine ⟨k, hk, ?_⟩
  rcases hg.mid_edge hk he hwe (by rw [hlw]; exact hk1') (by rw [hlw]; exact hk2') with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg.class_axis hk hA hwe
  · exact hg.class_edge hk hA hwe
  · exact hg.class_z1n1 hk hA hwe
  · exact hg.class_top hk hA hwe
  · exact hg.class_n0z0 hk hA hwe
  · exact hg.class_wall hk hA hwe

end Main

end Input

end ArtGallery.Sec5.Corridor

end
