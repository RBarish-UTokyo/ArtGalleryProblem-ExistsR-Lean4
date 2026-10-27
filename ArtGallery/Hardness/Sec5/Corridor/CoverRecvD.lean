module

public import ArtGallery.Hardness.Sec5.Corridor.CoverRecvC

/-!
# Section 5: corridors — the receivers see the umbra through the window

`Good.recv_seg`: for a point `z` of the umbra piece of pair `k` with `det(q, c1, z) ≤ 0`
(`q` the receiver of pair `k` at offset `t ∈ [0, 3/2]`), the segment `q z` crosses the window at a
point `w` and `[w, z]` lies in the corridor region.
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ}

section Recv

variable (hg : I.Good N)
include hg

/-- Points of the window in local coordinates. -/
theorem Good.window_coords {w : Point} (hw : w ∈ I.window) :
    I.lXR w = 8 * I.S ∧ -(8 * (I.S : ℝ)) ≤ I.lYR w ∧ I.lYR w ≤ -(8 * I.S) + 12 := by
  obtain ⟨μ, h0, h1, rfl⟩ := hw
  have hρ := hg.rhoR_pos
  have hS : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
  rw [ratPoint_c1', ratPoint_d1']
  refine ⟨by simp only [lXR]; ring, ?_, ?_⟩
  · simp only [lYR]
    have h := mul_nonneg (mul_nonneg hS.le hρ.le) h0
    nlinarith
  · simp only [lYR, rhoR_eq]
    have : 8 * (I.S : ℝ) * (μ * (3 / (2 * I.S))) = 12 * μ := by field_simp; ring
    nlinarith

variable {k : ℕ} (hk : k < I.np)
include hk

/-- A point of the receiver's sight segment from the window to the umbra lies in the corridor
region. -/
theorem Good.recv_point {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) {z w s : Point}
    (hz : z ∈ hpSet (I.umbraFs k)) (hw : w ∈ I.window)
    (hwq : w ∈ ArtGallery.segment ((I.umbraR k).q t) z) (hs : s ∈ ArtGallery.segment w z) :
    s ∈ I.poly.filled := by
  obtain ⟨zX1, zX2, zY1, zY2⟩ := hg.umbra_box hk hz
  obtain ⟨cz1, cz2⟩ := hg.recv_cone hk ht0 ht1 hz
  have hzmem := hz
  rw [mem_umbra_iff] at hzmem
  obtain ⟨zA, zE, zY, zW, zX, zN, zH⟩ := hzmem
  obtain ⟨wx, wy1, wy2⟩ := hg.window_coords hw
  obtain ⟨l1, l2, r1, r2, hN, hS, hww⟩ := hg.pairR hk
  obtain ⟨-, -, hS1, -, hSp, h64⟩ := hg.S_big
  obtain ⟨z0x, z0y⟩ := hg.rl_z0 hk
  obtain ⟨z1x, z1y⟩ := hg.rl_z1 hk
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw2
  set q := (I.umbraR k).q t
  -- `s` on the sight line from `q`
  have hsqz : s ∈ ArtGallery.segment q z :=
    Geometry.segment_subset_of_convex (Geometry.segment_convex q z) hwq
      (Geometry.right_mem_segment q z) hs
  have hray : ∀ x ∈ ArtGallery.segment q z, ∀ a : Point, 0 ≤ ArtGallery.det q a z →
      0 ≤ ArtGallery.det q a x := by
    rintro x ⟨μ, hμ0, -, rfl⟩ a ha
    have : ArtGallery.det q a (q.1 + μ * (z.1 - q.1), q.2 + μ * (z.2 - q.2)) =
        μ * ArtGallery.det q a z := by simp only [ArtGallery.det]; ring
    rw [this]; exact mul_nonneg hμ0 ha
  -- convexity facts on `[w, z]`
  have hconv : ∀ f : Aff, ∀ c : ℝ, c ≤ f.ev w → c ≤ f.ev z → c ≤ f.ev s :=
    fun f c h1 h2 => f.ge_ev_of_segment hs h1 h2
  have hconv' : ∀ f : Aff, ∀ c : ℝ, f.ev w ≤ c → f.ev z ≤ c → f.ev s ≤ c :=
    fun f c h1 h2 => f.ev_le_of_segment hs h1 h2
  have hsH : -(8 * (I.S : ℝ)) ≤ I.lYR s := by
    have := hconv (I.cA 0 1 0) (-(8 * I.S)) (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
    rw [ev_cA] at this; linarith
  have hsY : I.lYR s ≤ I.lYR (ratPoint (I.z1 k)) := by
    have := hconv' (I.cA 0 1 0) (I.lYR (ratPoint (I.z1 k))) (by rw [ev_cA, z1y]; linarith)
      (by rw [ev_cA]; linarith)
    rw [ev_cA] at this; linarith
  have hsXz : I.lXR z ≤ I.lXR s := by
    have := hconv (I.cA 1 0 0) (I.lXR z) (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
    rw [ev_cA] at this; linarith
  have hsX8 : I.lXR s ≤ 8 * I.S := by
    have := hconv' (I.cA 1 0 0) (8 * I.S) (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
    rw [ev_cA] at this; linarith
  have hsW : 0 ≤ ArtGallery.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) s := by
    have hwW := hg.wall_quadrant hk (P := w) (by rw [wx, z0x]; linarith) (by rw [z0y]; linarith)
    have := hconv (Aff.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k))) 0
      (by rw [Aff.ev_det]; exact hwW) (by rw [Aff.ev_det]; exact zW)
    rwa [Aff.ev_det] at this
  rcases le_or_gt 0 (I.AR k s) with hA | hA
  · -- above the axis: the umbra piece
    have hAw := hg.AR_window_neg hk hw
    obtain ⟨a, haseg, hav⟩ := exists_mem_segment_ev_eq (I.cA (-((I.hh k : ℚ) : ℝ))
      ((I.DD k : ℚ) : ℝ) (-(8 * I.S * ((I.gg k : ℚ) : ℝ)))) (g := w) (z := z) (c := 0)
      (by rw [← AR_eq_cA]; exact hAw.le) (by rw [← AR_eq_cA]; exact zA)
    rw [← AR_eq_cA] at hav
    have hsa : s ∈ ArtGallery.segment a z :=
      mem_segment_of_ev (I.cA (-((I.hh k : ℚ) : ℝ)) ((I.DD k : ℚ) : ℝ)
        (-(8 * I.S * ((I.gg k : ℚ) : ℝ)))) (by rw [← AR_eq_cA, ← AR_eq_cA, hav]; exact hAw)
        haseg hs (by rw [← AR_eq_cA, ← AR_eq_cA, hav]; exact hA)
    have haq : a ∈ ArtGallery.segment q z :=
      Geometry.segment_subset_of_convex (Geometry.segment_convex q z) hwq
        (Geometry.right_mem_segment q z) haseg
    obtain ⟨hax, hae⟩ := hg.axis_pt_west hk ht0 ht1 hav (hray a haq _ cz1)
    have hsE : 0 ≤ ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)) s := by
      have := (Aff.det (ratPoint (I.zp k)) (ratPoint (I.z1 k))).ge_ev_of_segment hsa (c := 0)
        (by rw [Aff.ev_det]; exact hae) (by rw [Aff.ev_det]; exact zE)
      rwa [Aff.ev_det] at this
    have hsXp : I.lXR s ≤ I.lXR (ratPoint (I.zp k)) := by
      have := (I.cA 1 0 0).ev_le_of_segment hsa (c := I.lXR (ratPoint (I.zp k)))
        (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
      rw [ev_cA] at this; linarith
    refine hg.umbra_subset hk ?_
    rw [mem_umbra_iff]
    exact ⟨hA, hsE, hsY, hsW, hsXp, zN.trans hsXz, hsH⟩
  · by_cases hxp : I.lXR s ≤ I.lXR (ratPoint (I.sgPt k))
    · refine hg.strip_subset hk ?_
      rw [mem_strip_iff]
      exact ⟨hxp, zN.trans hsXz, hsH, hA.le, hsW⟩
    · push Not at hxp
      have hk1 : 1 ≤ k := by
        by_contra h0; push Not at h0
        have : k = 0 := by omega
        subst this; rw [rl_sgPt_zero] at hxp; linarith
      obtain ⟨j, hjk, hj1, hj2⟩ := hg.strip_east hk hsX8 (zN.trans hsXz)
      have hjk' : j < k := by
        rcases hjk.lt_or_eq with h | h
        · exact h
        · subst h; linarith
      have hqv := hray s hsqz _ (cz2 hk1)
      rcases (show j + 1 = k ∨ (j = 0 ∧ k = 2) by have := hg.np_le; omega) with h | ⟨rfl, rfl⟩
      · subst h
        exact hg.recv_east_adj hk ht0 ht1 hqv hj1 hj2 hsH
      · exact hg.recv_east_far hk ht0 ht1 hqv hj1 hj2 hsH

/-- **The receiver sees the umbra through the window.** -/
theorem Good.recv_seg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) {z : Point}
    (hz : z ∈ hpSet (I.umbraFs k))
    (hc1 : ArtGallery.det ((I.umbraR k).q t) (ratPoint (c1 I.S I.H)) z ≤ 0) :
    ∃ w ∈ I.window, w ∈ ArtGallery.segment ((I.umbraR k).q t) z ∧
      ArtGallery.segment w z ⊆ I.poly.filled := by
  obtain ⟨w, hw, hwq⟩ := hg.recv_window hk ht0 ht1 hz hc1
  exact ⟨w, hw, hwq, fun s hs => hg.recv_point hk ht0 ht1 hz hw hwq hs⟩

end Recv

end Input

end ArtGallery.Sec5.Corridor

end
