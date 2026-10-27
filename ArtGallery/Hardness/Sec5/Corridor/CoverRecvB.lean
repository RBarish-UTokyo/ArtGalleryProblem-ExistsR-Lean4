module

public import ArtGallery.Hardness.Sec5.Corridor.CoverRecvA

/-!
# Section 5: corridors — the receiver's view of the umbra (cone and valley facts)

* `Good.recv_cone`: every point of the umbra piece is left of `q → z'_k` and (for `k ≥ 1`) left
  of `q → v_k` (from the receiver conditions at `z'_k`, `z1`, by `det_cone` at the vertex `z'_k`);
* `Good.below_valley`: a point left of `q → v_k` east of the valley is below the line of slope
  `−999/1000` through `v_k`;
* `Good.AR_neg_of_line`: points below a line of slope `−m` (`1/2 ≤ m ≤ 1`) east of a bound in the
  window are below the axis.
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ}

/-- A bracket `A h − D B` with a dominant negative term. -/
theorem bracket_neg {S N A B h D : ℝ} (hN : 2 ≤ N) (hS : 100000 * N ≤ S) (hD : S ≤ D)
    (hh : |h| ≤ 3 * N + 50) (hA : |A| ≤ 17 * S) (hB : 15 * S ≤ B) :
    A * h - D * B < 0 := by
  have hS0 : 200000 ≤ S := by linarith
  have h1 : A * h ≤ 17 * S * (3 * N + 50) := by
    have := abs_mul A h
    have := le_abs_self (A * h)
    have := mul_le_mul hA hh (abs_nonneg _) (by linarith)
    linarith
  have h2 : S * (15 * S) ≤ D * B :=
    mul_le_mul hD hB (by linarith) (by linarith)
  have h3 : 17 * S * (3 * N + 50) < S * (15 * S) := by nlinarith
  linarith

/-- A bracket `A h − D B` with a small `A` and `B ≥ 12`. -/
theorem bracket_neg' {S N A B h D : ℝ} (hN : 2 ≤ N) (hS : 100000 * N ≤ S) (hD : S ≤ D)
    (hh : |h| ≤ 3 * N + 50) (hA : |A| ≤ 14) (hB : 12 ≤ B) : A * h - D * B < 0 := by
  have h1 : A * h ≤ 14 * (3 * N + 50) := by
    have := abs_mul A h
    have := le_abs_self (A * h)
    have := mul_le_mul hA hh (abs_nonneg _) (by norm_num)
    linarith
  have h2 : S * 12 ≤ D * B := mul_le_mul hD hB (by norm_num) (by linarith)
  nlinarith

section Recv

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

/-- The abscissa of `p_k` is far east of `z'_k`. -/
theorem Good.sg_east_zp :
    I.lXR (ratPoint (I.zp k)) + 30 ≤ I.lXR (ratPoint (I.sgPt k)) := by
  obtain ⟨zx, -, -, -, -⟩ := hg.rl_zp hk
  obtain ⟨l1, l2, r1, r2, hN, hS, hw⟩ := hg.pairR hk
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at zx hw2
  obtain ⟨-, -, hS1, -⟩ := hg.S_big
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0; rw [rl_sgPt_zero]; nlinarith
  · rw [(hg.rl_sgPt hk h0).1]
    have := hg.lw_succ (j := k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at this
    linarith

/-- The edge `z'_k → z1` turns clockwise into the axis direction `z'_k → p_k`. -/
theorem Good.edge_turn :
    ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)) (ratPoint (I.sgPt k)) < 0 := by
  obtain ⟨hN, -, hS1, -, -, h64⟩ := hg.S_big
  obtain ⟨hD1, -⟩ := hg.DDR_bounds hk
  have hh := hg.hhR_abs hk
  obtain ⟨z1x, z1y⟩ := hg.rl_z1 hk
  obtain ⟨zx, zy, -, -, zA0⟩ := hg.rl_zp hk
  rw [abs_le] at zx zy
  have hpz := hg.sg_east_zp hk
  have hrel := axis_rel (I := I) (k := k) (hg.AR_sgPt hk) zA0
  have hDp : (0 : ℝ) < ((I.DD k : ℚ) : ℝ) := by linarith
  have e : 64 * (I.S : ℝ) ^ 2 * ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k))
      (ratPoint (I.sgPt k)) * ((I.DD k : ℚ) : ℝ) =
      (I.lXR (ratPoint (I.sgPt k)) - I.lXR (ratPoint (I.zp k))) *
        ((I.lXR (ratPoint (I.z1 k)) - I.lXR (ratPoint (I.zp k))) * ((I.hh k : ℚ) : ℝ) -
          ((I.DD k : ℚ) : ℝ) * (I.lYR (ratPoint (I.z1 k)) - I.lYR (ratPoint (I.zp k)))) := by
    rw [det_lXR]; linear_combination (I.lXR (ratPoint (I.z1 k)) - I.lXR (ratPoint (I.zp k))) * hrel
  have hb := bracket_neg' hN hS1 hD1 hh (A := I.lXR (ratPoint (I.z1 k)) - I.lXR (ratPoint (I.zp k)))
    (B := I.lYR (ratPoint (I.z1 k)) - I.lYR (ratPoint (I.zp k)))
    (by rw [abs_le]; constructor <;> linarith) (by linarith)
  have hneg : 64 * (I.S : ℝ) ^ 2 * ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k))
      (ratPoint (I.sgPt k)) * ((I.DD k : ℚ) : ℝ) < 0 := by
    rw [e]; exact mul_neg_of_pos_of_neg (by linarith) hb
  by_contra hc; push Not at hc
  have := mul_nonneg (mul_nonneg h64.le hc) hDp.le
  linarith

/-- Above the axis: left of `z'_k → p_k`. -/
theorem Good.above_axis_det {z : Point} (hA : 0 ≤ I.AR k z) :
    0 ≤ ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.sgPt k)) z := by
  obtain ⟨-, -, -, -, hSp, h64⟩ := hg.S_big
  obtain ⟨hD1, -⟩ := hg.DDR_bounds hk
  have hpz := hg.sg_east_zp hk
  have e := hg.AR_det hk z
  have hDp : (0 : ℝ) < ((I.DD k : ℚ) : ℝ) := by linarith
  have h1 : 0 ≤ 64 * (I.S : ℝ) ^ 2 * ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.sgPt k)) z *
      ((I.DD k : ℚ) : ℝ) := by rw [e]; exact mul_nonneg (by linarith) hA
  have h2 : 0 ≤ 64 * (I.S : ℝ) ^ 2 * ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.sgPt k)) z :=
    nonneg_of_mul_nonneg_c hDp (by linarith [mul_comm (64 * (I.S : ℝ) ^ 2 *
      ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.sgPt k)) z) ((I.DD k : ℚ) : ℝ)])
  exact nonneg_of_mul_nonneg_c h64 h2

/-- A direction from the receiver, clockwise of the axis direction: the sign condition `h5` of
`det_cone`, for a point `a` with `B = lY a − lY q ≥ 16 S − 2000`. -/
theorem Good.recv_dir {t : ℝ} {a : Point} (hax : |I.lXR a - I.lXR ((I.umbraR k).q t)| ≤
      17 * I.S) (hay : 15 * I.S ≤ I.lYR a - I.lYR ((I.umbraR k).q t)) :
    (a.1 - ((I.umbraR k).q t).1) * ((ratPoint (I.sgPt k)).2 - (ratPoint (I.zp k)).2) -
      (a.2 - ((I.umbraR k).q t).2) * ((ratPoint (I.sgPt k)).1 - (ratPoint (I.zp k)).1) ≤ 0 := by
  obtain ⟨hN, -, hS1, -, -, h64⟩ := hg.S_big
  obtain ⟨hD1, -⟩ := hg.DDR_bounds hk
  have hh := hg.hhR_abs hk
  obtain ⟨-, -, -, -, zA0⟩ := hg.rl_zp hk
  have hpz := hg.sg_east_zp hk
  have hrel := axis_rel (I := I) (k := k) (hg.AR_sgPt hk) zA0
  have hDp : (0 : ℝ) < ((I.DD k : ℚ) : ℝ) := by linarith
  set q := (I.umbraR k).q t
  have e : 64 * (I.S : ℝ) ^ 2 * ((a.1 - q.1) * ((ratPoint (I.sgPt k)).2 - (ratPoint (I.zp k)).2) -
      (a.2 - q.2) * ((ratPoint (I.sgPt k)).1 - (ratPoint (I.zp k)).1)) * ((I.DD k : ℚ) : ℝ) =
      (I.lXR (ratPoint (I.sgPt k)) - I.lXR (ratPoint (I.zp k))) *
        ((I.lXR a - I.lXR q) * ((I.hh k : ℚ) : ℝ) - ((I.DD k : ℚ) : ℝ) * (I.lYR a - I.lYR q)) := by
    have e2 : 64 * (I.S : ℝ) ^ 2 * ((a.1 - q.1) * ((ratPoint (I.sgPt k)).2 - (ratPoint (I.zp k)).2) -
        (a.2 - q.2) * ((ratPoint (I.sgPt k)).1 - (ratPoint (I.zp k)).1)) =
        (I.lXR a - I.lXR q) * (I.lYR (ratPoint (I.sgPt k)) - I.lYR (ratPoint (I.zp k))) -
          (I.lYR a - I.lYR q) * (I.lXR (ratPoint (I.sgPt k)) - I.lXR (ratPoint (I.zp k))) := by
      simp only [lXR, lYR]; ring
    rw [e2]; linear_combination (I.lXR a - I.lXR q) * hrel
  have hb := bracket_neg hN hS1 hD1 hh hax hay
  have hneg : 64 * (I.S : ℝ) ^ 2 * ((a.1 - q.1) * ((ratPoint (I.sgPt k)).2 - (ratPoint (I.zp k)).2) -
      (a.2 - q.2) * ((ratPoint (I.sgPt k)).1 - (ratPoint (I.zp k)).1)) * ((I.DD k : ℚ) : ℝ) < 0 := by
    rw [e]; exact mul_neg_of_pos_of_neg (by linarith) hb
  by_contra hc; push Not at hc
  have := mul_pos (mul_pos h64 hc) hDp
  linarith

/-- The receiver is far south-east of the corridor's middle. -/
theorem Good.recv_far {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) {a : Point}
    (hax : |I.lXR a| ≤ 1000 * N) (hay : |I.lYR a| ≤ 1000 * N) :
    |I.lXR a - I.lXR ((I.umbraR k).q t)| ≤ 17 * I.S ∧
      15 * I.S ≤ I.lYR a - I.lYR ((I.umbraR k).q t) := by
  obtain ⟨qx, qy⟩ := hg.rl_recv hk t
  obtain ⟨u1, u2, w1, w2, -⟩ := hg.recv_atoms hk
  obtain ⟨hN, -, hS1, -, -, -⟩ := hg.S_big
  rw [abs_le] at hax hay
  rw [qx, qy, abs_le]
  refine ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith⟩

/-- The valley direction and the edge: the sign condition `h4` of `det_cone` for `a = v_k`. -/
theorem Good.recv_valley_h4 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) (hk1 : 1 ≤ k) :
    0 ≤ ((ratPoint (I.valley k)).1 - ((I.umbraR k).q t).1) *
        ((ratPoint (I.z1 k)).2 - (ratPoint (I.zp k)).2) -
      ((ratPoint (I.valley k)).2 - ((I.umbraR k).q t).2) *
        ((ratPoint (I.z1 k)).1 - (ratPoint (I.zp k)).1) := by
  obtain ⟨hN, -, hS1, -, -, h64⟩ := hg.S_big
  obtain ⟨z1x, z1y⟩ := hg.rl_z1 hk
  obtain ⟨zx, -, zξ1, zξ2, -⟩ := hg.rl_zp hk
  obtain ⟨vx, vy⟩ := hg.rl_valley hk hk1
  obtain ⟨qx, qy⟩ := hg.rl_recv hk t
  obtain ⟨u1, u2, w1, w2, hr⟩ := hg.recv_atoms hk
  obtain ⟨l1, l2, r1, r2, -, -, hw⟩ := hg.pairR hk
  have hl := hg.lwE_bound (k := k - 1) (by omega)
  have hl1 : (30 : ℝ) ≤ I.lwR (k - 1) := by
    have := rat_cast_le_of hl.1; simp only [lwR]; push_cast at this; exact this
  have hl2 : I.lwR (k - 1) ≤ 136 * N + 10 := by
    have := rat_cast_le_of hl.2; simp only [lwR]; push_cast at this; exact this
  rw [abs_le] at zx
  refine nonneg_of_mul_nonneg_c h64 ?_
  have e : 64 * (I.S : ℝ) ^ 2 * (((ratPoint (I.valley k)).1 - ((I.umbraR k).q t).1) *
        ((ratPoint (I.z1 k)).2 - (ratPoint (I.zp k)).2) -
      ((ratPoint (I.valley k)).2 - ((I.umbraR k).q t).2) *
        ((ratPoint (I.z1 k)).1 - (ratPoint (I.zp k)).1)) =
      ((I.lXR (ratPoint (I.zp k)) + I.lYR (ratPoint (I.zp k))) - I.rwR k) *
          (I.lXR ((I.umbraR k).q t) - I.lXR (ratPoint (I.valley k))) +
        (I.lXR (ratPoint (I.zp k)) - I.lXR (ratPoint (I.z1 k))) *
          (I.rwR k + 1 / 2 - (I.lXR ((I.umbraR k).q t) + I.lYR ((I.umbraR k).q t))) := by
    have e2 : 64 * (I.S : ℝ) ^ 2 * (((ratPoint (I.valley k)).1 - ((I.umbraR k).q t).1) *
        ((ratPoint (I.z1 k)).2 - (ratPoint (I.zp k)).2) -
      ((ratPoint (I.valley k)).2 - ((I.umbraR k).q t).2) *
        ((ratPoint (I.z1 k)).1 - (ratPoint (I.zp k)).1)) =
        (I.lXR (ratPoint (I.valley k)) - I.lXR ((I.umbraR k).q t)) *
          (I.lYR (ratPoint (I.z1 k)) - I.lYR (ratPoint (I.zp k))) -
        (I.lYR (ratPoint (I.valley k)) - I.lYR ((I.umbraR k).q t)) *
          (I.lXR (ratPoint (I.z1 k)) - I.lXR (ratPoint (I.zp k))) := by
      simp only [lXR, lYR]; ring
    rw [e2]
    have hv : I.lYR (ratPoint (I.valley k)) = I.rwR k + 1 / 2 - I.lXR (ratPoint (I.valley k)) := by
      rw [vx, vy]; ring
    have h1 : I.lYR (ratPoint (I.z1 k)) = I.rwR k - I.lXR (ratPoint (I.z1 k)) := by
      rw [z1x, z1y]; ring
    rw [hv, h1]; ring
  rw [e]
  have b1 : 1 / 16 ≤ (I.lXR (ratPoint (I.zp k)) + I.lYR (ratPoint (I.zp k))) - I.rwR k := by
    linarith
  have b2 : 15 * (I.S : ℝ) ≤ I.lXR ((I.umbraR k).q t) - I.lXR (ratPoint (I.valley k)) := by
    rw [qx, vx]; nlinarith
  have b3 : 0 ≤ I.lXR (ratPoint (I.zp k)) - I.lXR (ratPoint (I.z1 k)) := by rw [z1x]; linarith
  have b4 : I.lXR (ratPoint (I.zp k)) - I.lXR (ratPoint (I.z1 k)) ≤ 14 := by rw [z1x]; linarith
  have b5 : |I.rwR k + 1 / 2 - (I.lXR ((I.umbraR k).q t) + I.lYR ((I.umbraR k).q t))| ≤ 2000 := by
    rw [qx, qy, abs_le]; constructor <;> linarith
  have hSp : (0 : ℝ) < I.S := by linarith
  have c1 := mul_le_mul b1 b2 (by positivity) (by linarith)
  have c2 : |(I.lXR (ratPoint (I.zp k)) - I.lXR (ratPoint (I.z1 k))) *
      (I.rwR k + 1 / 2 - (I.lXR ((I.umbraR k).q t) + I.lYR ((I.umbraR k).q t)))| ≤ 14 * 2000 := by
    rw [abs_mul]; exact mul_le_mul (by rw [abs_of_nonneg b3]; exact b4) b5 (abs_nonneg _)
      (by norm_num)
  rw [abs_le] at c2
  nlinarith

/-- The cone lemma for the valley. -/
theorem Good.recv_cone_valley {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) (hk1 : 1 ≤ k) {z : Point}
    (h1 : ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)) (ratPoint (I.sgPt k)) < 0)
    (zE : 0 ≤ ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)) z)
    (h3 : 0 ≤ ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.sgPt k)) z) :
    ArtGallery.det ((I.umbraR k).q t) (ratPoint (I.valley k)) (ratPoint (I.zp k)) ≤
      ArtGallery.det ((I.umbraR k).q t) (ratPoint (I.valley k)) z := by
  obtain ⟨vx, vy⟩ := hg.rl_valley hk hk1
  have hwv := hg.window_valley hk hk1
  have hwv' := rat_cast_le_of hwv; push_cast at hwv'
  obtain ⟨l1, l2, r1, r2, hN, hS, hw⟩ := hg.pairR hk
  have hl := hg.lwE_bound (k := k - 1) (by omega)
  have hl1 : (30 : ℝ) ≤ I.lwR (k - 1) := by
    have := rat_cast_le_of hl.1; simp only [lwR]; push_cast at this; exact this
  have hl2 : I.lwR (k - 1) ≤ 136 * N + 10 := by
    have := rat_cast_le_of hl.2; simp only [lwR]; push_cast at this; exact this
  obtain ⟨f1, f2⟩ := hg.recv_far hk ht0 ht1 (a := ratPoint (I.valley k))
    (by rw [vx, abs_le]; constructor <;> linarith) (by rw [vy, abs_le]; constructor <;> linarith)
  exact det_cone h1 zE h3 (hg.recv_valley_h4 hk ht0 ht1 hk1) (hg.recv_dir hk f1 f2)

/-- **The receiver sees the umbra past `z'_k` and below the valley.** -/
theorem Good.recv_cone {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) {z : Point}
    (hz : z ∈ hpSet (I.umbraFs k)) :
    0 ≤ ArtGallery.det ((I.umbraR k).q t) (ratPoint (I.zp k)) z ∧
      (1 ≤ k → 0 ≤ ArtGallery.det ((I.umbraR k).q t) (ratPoint (I.valley k)) z) := by
  obtain ⟨c1, c2, c3⟩ := hg.recv_conds hk ht0 ht1
  rw [mem_umbra_iff] at hz
  obtain ⟨zA, zE, -, -, -, -, -⟩ := hz
  obtain ⟨-, -, -, -, -, h64⟩ := hg.S_big
  have h1 := hg.edge_turn hk
  have h3 := hg.above_axis_det hk zA
  obtain ⟨l1, l2, r1, r2, hN, hS, hw⟩ := hg.pairR hk
  obtain ⟨zx, zy, zξ1, zξ2, -⟩ := hg.rl_zp hk
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at zx zy hw2
  constructor
  · obtain ⟨f1, f2⟩ := hg.recv_far hk ht0 ht1 (a := ratPoint (I.zp k))
      (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> nlinarith)
    have h5 := hg.recv_dir hk f1 f2
    have key := det_cone (q := (I.umbraR k).q t) (a := ratPoint (I.zp k)) h1 zE h3 ?_ h5
    · have : ArtGallery.det ((I.umbraR k).q t) (ratPoint (I.zp k)) (ratPoint (I.zp k)) = 0 := by
        simp only [ArtGallery.det]; ring
      linarith
    · have e : ((ratPoint (I.zp k)).1 - ((I.umbraR k).q t).1) *
          ((ratPoint (I.z1 k)).2 - (ratPoint (I.zp k)).2) -
          ((ratPoint (I.zp k)).2 - ((I.umbraR k).q t).2) *
          ((ratPoint (I.z1 k)).1 - (ratPoint (I.zp k)).1) =
          ArtGallery.det ((I.umbraR k).q t) (ratPoint (I.zp k)) (ratPoint (I.z1 k)) := by
        simp only [ArtGallery.det]; ring
      rw [e]; exact c1
  · intro hk1
    exact le_trans (c3 hk1) (hg.recv_cone_valley hk ht0 ht1 hk1 h1 zE h3)

end Recv

end Input

end ArtGallery.Sec5.Corridor

end
