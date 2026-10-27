module

public import ArtGallery.Hardness.Sec5.Corridor.SGView

/-!
# Section 5, counting: the witness slots of different stationary guards of a corridor

The stationary guards `p_k` of a corridor are pinned by the tips of their two floor slots
(`q_a = slotTip k 2`, slope 2; `q_b = slotTip k 4`, slope 4).  The slope-2 cones are long: a
point seeing `q_b(j)` may see `q_a(k)` for a pair `k` east of `j`.  The pinning processes the
stationary guards from west to east (decreasing `k`), and what is needed is:

* `Good.sees_tip4_le`: every point seen from `q_b(j)` lies weakly below `p_j` (a segment from
  `q_b(j)` passing east of `p_j` crosses the vertical upper-wall edge `base_j → p_j`; one through
  `p_j` leaves the cone of the convex corner `p_j`);
* `Good.not_sees_tip4_tip2`: for `j < k` (pair `j` east of pair `k`) no point sees both
  `q_b(j)` and `q_a(k)` (such a point would lie `400ε` above `p_j`, by `kx_sep`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ} (hg : I.Good N) {P : Polygon} {a b : ℕ} (hP : P.Simple)
  (hL : P.InteriorLeft) (hC : CorridorAt P I a b)
include hg hP hL hC

/-- **The visibility set of the slope-4 tip lies below its stationary guard.** -/
theorem Good.sees_tip4_le {j : ℕ} (hj : j < I.np) {x : Point}
    (hx : P.Sees x (ratPoint (I.slotTip j 4))) : x.2 ≤ ((I.sgPt j).2 : ℝ) := by
  have hn : 0 < P.n := by have := hP.1; omega
  have hc := hg.sees_tip4_cone hP hL hC hj hx
  have e4 := sgPt_on_slot4 (I := I) j
  have cfg := hg.sgConfig hj
  have he := hg.eps_real
  obtain ⟨-, r2, -⟩ := slot4_ratPoint (I := I) j
  set px : ℝ := ((I.sgPt j).1 : ℝ)
  set py : ℝ := ((I.sgPt j).2 : ℝ)
  set κ : ℝ := (I.kx j 4 : ℝ)
  set H : ℝ := (I.H : ℝ)
  set ε : ℝ := (I.ε : ℝ)
  have hh1 : (1 / 2 : ℝ) ≤ py - H := by
    have : ((1 / 2 : ℚ) : ℝ) ≤ (((I.sgPt j).2 - I.H : ℚ) : ℝ) := by exact_mod_cast cfg.hh1
    push_cast at this; linarith
  have hh2 : py - H ≤ 3 / 2 := by
    have : (((I.sgPt j).2 - I.H : ℚ) : ℝ) ≤ ((3 / 2 : ℚ) : ℝ) := by exact_mod_cast cfg.hh2
    push_cast at this; linarith
  have hpu : 37 * ε ≤ py - ((I.base j).2 : ℝ) := by
    have : ((37 * I.ε : ℚ) : ℝ) ≤ (((I.sgPt j).2 - (I.base j).2 : ℚ) : ℝ) := by
      exact_mod_cast cfg.hpu
    push_cast at this; linarith
  by_contra hcon
  push Not at hcon
  obtain ⟨c1, c2⟩ := hc
  rw [r2] at hx
  -- the guard and the base of its pocket as vertices
  obtain ⟨A₁, A₂, hA⟩ := chainAfter_infix_sg hj
  obtain ⟨hp₁, -, -, hu, hp₀⟩ := vtx_triple hn hC.after hA
  have hbx : ((I.base j).1 : ℝ) = px := by rw [show (I.base j).1 = (I.sgPt j).1 from rfl]
  have hx' := Polygon.sees_comm.1 hx
  set uy : ℝ := ((I.base j).2 : ℝ)
  rcases eq_or_lt_of_le c1 with heq | hlt
  · -- the segment passes through `p_j`
    have hx1 : x.1 - (κ - 1 / 16) = (x.2 - (H - 1 / 4)) / 4 := by linarith
    have hd : x.2 - (H - 1 / 4) ≠ 0 := by linarith
    have hseg : ratPoint (I.sgPt j) ∈ ArtGallery.segment (κ - 1 / 16, H - 1 / 4) x := by
      refine Geometry.mem_segment_iff_lerp.2 ⟨(py - (H - 1 / 4)) / (x.2 - (H - 1 / 4)),
        div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).2 (by linarith), ?_⟩
      ext
      · simp only [ratPoint_fst, Geometry.lerp_fst]
        rw [hx1, div_mul_div_comm, mul_comm (py - (H - 1 / 4)), ← div_mul_div_comm,
          div_self hd, one_mul]
        linarith
      · simp only [ratPoint_snd, Geometry.lerp_snd]
        rw [div_mul_cancel₀ _ hd]
        ring
    have hsub : P.Sees (ratPoint (I.sgPt j)) x := fun z hz => hx'
      (Geometry.segment_subset_of_convex (Geometry.segment_convex _ _) hseg
        (Geometry.right_mem_segment _ _) hz)
    have := (hg.sg_cone hP hL hC hj hsub).1
    simp only [ratPoint_fst] at this
    linarith
  · -- the segment crosses the vertical edge `base_j → p_j`
    have hb : ratPoint (I.base j) = (px, uy) := by
      ext
      · simp only [ratPoint_fst]; exact hbx
      · rfl
    have hp : ratPoint (I.sgPt j) = (px, py) := rfl
    refine Polygon.not_sees_of_proper_cross hP
      (i := (b + A₁.length) % P.n) (Nat.mod_lt _ hn) ?_ ?_ hx'
    · rw [hu, hp₀, hb, hp]
      have d1 : det (px, uy) (px, py) (κ - 1 / 16, H - 1 / 4) =
          (px - (κ - 1 / 16)) * (py - uy) := by simp only [det]; ring
      have d2 : det (px, uy) (px, py) x = -((x.1 - px) * (py - uy)) := by simp only [det]; ring
      rw [d1, d2]
      have h1 : 0 < x.1 - px := by linarith
      have h2 : 0 < py - uy := by linarith
      have h3 : 0 < px - (κ - 1 / 16) := by linarith
      have := mul_pos (mul_pos h3 h2) (mul_pos h1 h2)
      nlinarith
    · rw [hu, hp₀, hb, hp]
      obtain ⟨A, hA⟩ : ∃ A, A = x.1 - (κ - 1 / 16) := ⟨_, rfl⟩
      obtain ⟨B, hBd⟩ : ∃ B, B = x.2 - (H - 1 / 4) := ⟨_, rfl⟩
      obtain ⟨c, hcd⟩ : ∃ c, c = px - (κ - 1 / 16) := ⟨_, rfl⟩
      have d1 : det (κ - 1 / 16, H - 1 / 4) x (px, uy) = A * (uy - (H - 1 / 4)) - c * B := by
        rw [hA, hBd, hcd]; simp only [det]; try ring
      have d2 : det (κ - 1 / 16, H - 1 / 4) x (px, py) = A * (py - (H - 1 / 4)) - c * B := by
        rw [hA, hBd, hcd]; simp only [det]; try ring
      rw [d1, d2]
      subst hA hBd hcd
      have hB : 0 < x.2 - (H - 1 / 4) := by linarith
      set A := x.1 - (κ - 1 / 16) with hA
      set B := x.2 - (H - 1 / 4) with hBd
      set c := px - (κ - 1 / 16) with hcd
      have hc4 : py - (H - 1 / 4) = 4 * c := by rw [hcd]; linarith
      have hc0 : 0 < c := by rw [hcd]; linarith
      have hc1 : c ≤ 7 / 16 := by rw [hcd]; linarith
      have h4AB : 0 < 4 * A - B := by rw [hA, hBd]; linarith
      have h4AB' : 4 * A - B ≤ 2 * ε * B := by rw [hA, hBd]; linarith
      have hA4 : B / 4 ≤ A := by rw [hA, hBd]; linarith
      have hpos : 0 < A * (py - (H - 1 / 4)) - c * B := by
        rw [hc4]; nlinarith
      have e : A * (uy - (H - 1 / 4)) - c * B = c * (4 * A - B) - A * (py - uy) := by
        have : uy - (H - 1 / 4) = 4 * c - (py - uy) := by rw [hcd]; linarith
        rw [this]; ring
      have hneg : A * (uy - (H - 1 / 4)) - c * B < 0 := by
        rw [e]
        have hA0 : 0 < A := by linarith
        have k1 : c * (4 * A - B) ≤ 7 / 8 * (ε * B) :=
          calc c * (4 * A - B) ≤ c * (2 * ε * B) := mul_le_mul_of_nonneg_left h4AB' hc0.le
            _ ≤ 7 / 16 * (2 * ε * B) :=
              mul_le_mul_of_nonneg_right hc1 (by have := mul_pos he.1 hB; linarith)
            _ = 7 / 8 * (ε * B) := by ring
        have k2 : 37 * (ε * A) ≤ A * (py - uy) :=
          calc 37 * (ε * A) = A * (37 * ε) := by ring
            _ ≤ A * (py - uy) := mul_le_mul_of_nonneg_left hpu hA0.le
        have k5 : ε * B ≤ 4 * (ε * A) :=
          calc ε * B = 4 * (ε * (B / 4)) := by ring
            _ ≤ 4 * (ε * A) := by
              have := mul_le_mul_of_nonneg_left hA4 he.1.le; linarith
        have k6 : 0 < ε * A := mul_pos he.1 hA0
        linarith
      exact mul_neg_of_neg_of_pos hneg hpos

/-- **Slope-4 and slope-2 witnesses of different pairs.** For a pair `j` east of the pair `k`
(`j < k`), no point sees both `q_b(j)` and `q_a(k)`. -/
theorem Good.not_sees_tip4_tip2 {j k : ℕ} (hjk : j < k) (hk : k < I.np) {x : Point}
    (h4 : P.Sees x (ratPoint (I.slotTip j 4))) : ¬ P.Sees x (ratPoint (I.slotTip k 2)) := by
  intro h2
  have hj : j < I.np := by omega
  have hle := hg.sees_tip4_le hP hL hC hj h4
  have c4 := (hg.sees_tip4_cone hP hL hC hj h4).1
  have c2 := (hg.sees_tip2_cone hP hL hC hk h2).2
  have e4 := sgPt_on_slot4 (I := I) j
  have e2 := sgPt_on_slot2 (I := I) j
  have hsep := hg.kx_sep (Or.inl rfl) hjk hk
  have hsep' : (I.kx k 2 : ℝ) + 100 * (I.ε : ℝ) ≤ (I.kx j 2 : ℝ) := by exact_mod_cast hsep
  have he := hg.eps_real
  linarith

end Input

end ArtGallery.Sec5.Corridor

end
