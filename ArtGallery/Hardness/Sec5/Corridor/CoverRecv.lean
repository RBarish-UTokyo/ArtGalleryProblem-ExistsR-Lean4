module

public import ArtGallery.Hardness.Sec5.Corridor.CoverRecvB

/-!
# Section 5: corridors — the receivers see the umbra through the window

For pair `k` and the receiver guard `q = m + (T_τ + (t, 0))/S` (`t ∈ [0, 3/2]`):

* `Good.recv_seg`: if `z` is a point of the umbra piece with `det(q, c1, z) ≤ 0` (on the
  receiver's side of its line through `c1`), the segment `q z` crosses the window `c1 d1` at a
  point `w`, and the segment `w z` lies in the corridor region: the part above the axis `A_k` lies
  in the umbra piece (it starts on the axis west of `z'_k`, since `z` is left of `q → z'_k`), the
  part below it in the strip piece of `k` or, east of the valley `v_k`, in the strips of the pairs
  `j < k` (the segment passes below the valley, since `z` is left of `q → v_k`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ}

/-- On a segment `[w, z]` along which an affine function increases from `f w` past `f a`, the
points with `f ≥ f a` lie on `[a, z]`. -/
theorem mem_segment_of_ev (f : Aff) {w z a s : Point} (hwa : f.ev w < f.ev a)
    (ha : a ∈ ArtGallery.segment w z) (hs : s ∈ ArtGallery.segment w z) (hfs : f.ev a ≤ f.ev s) :
    s ∈ ArtGallery.segment a z := by
  obtain ⟨α, hα0, hα1, rfl⟩ := ha
  obtain ⟨σ, hσ0, hσ1, rfl⟩ := hs
  rw [Aff.ev_lerp] at hwa hfs
  rw [Aff.ev_lerp] at hfs
  have hpos : 0 < f.ev z - f.ev w := by nlinarith
  have hασ : α ≤ σ := by nlinarith
  rcases hα1.lt_or_eq with h | h
  · refine ⟨(σ - α) / (1 - α), div_nonneg (by linarith) (by linarith),
      (div_le_one (by linarith)).2 (by linarith), ?_⟩
    ext <;> simp only <;> field_simp <;> ring
  · subst h
    have : σ = 1 := le_antisymm hσ1 hασ
    subst this
    exact ⟨0, le_rfl, zero_le_one, by ext <;> simp⟩

/-- **Below a line of slope `−m`, east of a bound: below the axis.** -/
theorem Good.AR_neg_of_line (hg : I.Good N) {k : ℕ} (hk : k < I.np) {s : Point}
    {X0 Y0 m Xmin : ℝ} (hm1 : 1 / 2 ≤ m) (hm2 : m ≤ 1) (hXm : |Xmin| ≤ 456 * N)
    (h1 : I.lYR s ≤ Y0 - m * (I.lXR s - X0)) (h2 : Xmin ≤ I.lXR s)
    (h3 : Y0 - m * (Xmin - X0) ≤ (I.lwR k + I.rwR k) / 2 - 17) : I.AR k s < 0 := by
  obtain ⟨E, hE, hEb⟩ := hg.AR_eq hk s
  obtain ⟨hD1, hD2⟩ := hg.DDR_bounds hk
  have hh := hg.hhR_abs hk
  obtain ⟨hN, hS, hS1, -, hSp, -⟩ := hg.S_big
  rw [abs_le] at hEb hh
  have hhX : |((I.hh k : ℚ) : ℝ) * Xmin| ≤ (3 * N + 50) * (456 * N) := by
    rw [abs_mul]; exact mul_le_mul (abs_le.2 hh) hXm (abs_nonneg _) (by linarith)
  rw [abs_le] at hhX
  have hDm : 0 ≤ ((I.DD k : ℚ) : ℝ) * m + ((I.hh k : ℚ) : ℝ) := by nlinarith
  have step : I.AR k s ≤ ((I.DD k : ℚ) : ℝ) * (Y0 - m * (Xmin - X0) -
      ((I.lwR k + I.rwR k) / 2 - 16)) - ((I.hh k : ℚ) : ℝ) * Xmin + E := by
    rw [hE]
    have a1 : ((I.DD k : ℚ) : ℝ) * I.lYR s ≤ ((I.DD k : ℚ) : ℝ) * (Y0 - m * (I.lXR s - X0)) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have a2 : 0 ≤ (((I.DD k : ℚ) : ℝ) * m + ((I.hh k : ℚ) : ℝ)) * (I.lXR s - Xmin) :=
      mul_nonneg hDm (by linarith)
    nlinarith
  have a3 : ((I.DD k : ℚ) : ℝ) * (Y0 - m * (Xmin - X0) - ((I.lwR k + I.rwR k) / 2 - 16)) ≤
      ((I.DD k : ℚ) : ℝ) * (-1) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have a4 : (3 * (N : ℝ) + 50) * (456 * N) + 4 * (17 * N + 100) * (14 * N + 50) < I.S := by
    rw [hS]; nlinarith
  linarith

section Recv

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

/-- Points of the umbra piece have `ξ ≤ r + 3/2`. -/
theorem Good.umbra_xi {z : Point} (hz : z ∈ hpSet (I.umbraFs k)) :
    I.lYR z + I.lXR z ≤ I.rwR k + 3 / 2 := by
  obtain ⟨zX1, zX2, -, -⟩ := hg.umbra_box hk hz
  rw [mem_umbra_iff] at hz
  obtain ⟨-, zE, -⟩ := hz
  have e := hg.edge_det hk z
  obtain ⟨z1x, -⟩ := hg.rl_z1 hk
  obtain ⟨zx, -, zξ1, zξ2, -⟩ := hg.rl_zp hk
  obtain ⟨-, -, -, -, -, h64⟩ := hg.S_big
  rw [abs_le] at zx
  have h := mul_nonneg h64.le zE
  rw [e, z1x] at h
  by_contra hc; push Not at hc
  nlinarith

/-- A point of the axis left of `q → z'_k` is west of `z'_k` and on the inner side of the edge
`z'_k → z1`. -/
theorem Good.axis_pt_west {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) {a : Point}
    (hA : I.AR k a = 0) (hq : 0 ≤ ArtGallery.det ((I.umbraR k).q t) (ratPoint (I.zp k)) a) :
    I.lXR a ≤ I.lXR (ratPoint (I.zp k)) ∧
      0 ≤ ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)) a := by
  obtain ⟨hN, -, hS1, -, hSp, h64⟩ := hg.S_big
  obtain ⟨hD1, -⟩ := hg.DDR_bounds hk
  have hh := hg.hhR_abs hk
  obtain ⟨z1x, z1y⟩ := hg.rl_z1 hk
  obtain ⟨zx, zy, -, -, zA0⟩ := hg.rl_zp hk
  obtain ⟨l1, l2, r1, r2, -, -, hw⟩ := hg.pairR hk
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at zx zy hw2
  have hrel := axis_rel (I := I) (k := k) hA zA0
  have hDp : (0 : ℝ) < ((I.DD k : ℚ) : ℝ) := by linarith
  set q := (I.umbraR k).q t
  obtain ⟨f1, f2⟩ := hg.recv_far hk ht0 ht1 (a := ratPoint (I.zp k))
    (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> nlinarith)
  -- `X_a ≤ X'`
  have hb := bracket_neg hN hS1 hD1 hh f1 f2
  have e1 : 64 * (I.S : ℝ) ^ 2 * ArtGallery.det q (ratPoint (I.zp k)) a * ((I.DD k : ℚ) : ℝ) =
      (I.lXR a - I.lXR (ratPoint (I.zp k))) * ((I.lXR (ratPoint (I.zp k)) - I.lXR q) *
        ((I.hh k : ℚ) : ℝ) - ((I.DD k : ℚ) : ℝ) * (I.lYR (ratPoint (I.zp k)) - I.lYR q)) := by
    rw [det_lXR]; linear_combination (I.lXR (ratPoint (I.zp k)) - I.lXR q) * hrel
  have hx : I.lXR a ≤ I.lXR (ratPoint (I.zp k)) := by
    by_contra hc; push Not at hc
    have : 64 * (I.S : ℝ) ^ 2 * ArtGallery.det q (ratPoint (I.zp k)) a * ((I.DD k : ℚ) : ℝ) < 0 := by
      rw [e1]; exact mul_neg_of_pos_of_neg (by linarith) hb
    have := mul_nonneg (mul_nonneg h64.le hq) hDp.le
    linarith
  refine ⟨hx, ?_⟩
  have hb' := bracket_neg' hN hS1 hD1 hh (A := I.lXR (ratPoint (I.z1 k)) - I.lXR (ratPoint (I.zp k)))
    (B := I.lYR (ratPoint (I.z1 k)) - I.lYR (ratPoint (I.zp k)))
    (by rw [abs_le]; constructor <;> linarith) (by linarith)
  have e2 : 64 * (I.S : ℝ) ^ 2 * ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)) a *
      ((I.DD k : ℚ) : ℝ) = (I.lXR a - I.lXR (ratPoint (I.zp k))) *
        ((I.lXR (ratPoint (I.z1 k)) - I.lXR (ratPoint (I.zp k))) * ((I.hh k : ℚ) : ℝ) -
          ((I.DD k : ℚ) : ℝ) * (I.lYR (ratPoint (I.z1 k)) - I.lYR (ratPoint (I.zp k)))) := by
    rw [det_lXR]; linear_combination (I.lXR (ratPoint (I.z1 k)) - I.lXR (ratPoint (I.zp k))) * hrel
  have : 0 ≤ 64 * (I.S : ℝ) ^ 2 * ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)) a *
      ((I.DD k : ℚ) : ℝ) := by
    rw [e2]; exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hb'.le
  have h2 := nonneg_of_mul_nonneg_c hDp (by rw [mul_comm]; exact this)
  exact nonneg_of_mul_nonneg_c h64 h2

/-- **Below the valley.**  A point left of `q → v_k` east of the valley is below the line of slope
`−(1 − 1/(500N))` through `v_k`. -/
theorem Good.below_valley {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) (hk1 : 1 ≤ k) {s : Point}
    (hq : 0 ≤ ArtGallery.det ((I.umbraR k).q t) (ratPoint (I.valley k)) s)
    (hx : I.lXR (ratPoint (I.valley k)) ≤ I.lXR s) :
    I.lYR s - I.lYR (ratPoint (I.valley k)) ≤
      -(1 - 1 / (500 * N)) * (I.lXR s - I.lXR (ratPoint (I.valley k))) := by
  obtain ⟨hN, -, hS1, -, hSp, h64⟩ := hg.S_big
  obtain ⟨vx, vy⟩ := hg.rl_valley hk hk1
  obtain ⟨qx, qy⟩ := hg.rl_recv hk t
  obtain ⟨u1, u2, w1, w2, hr⟩ := hg.recv_atoms hk
  obtain ⟨l1, l2, r1, r2, -, -, hw⟩ := hg.pairR hk
  have hl := hg.lwE_bound (k := k - 1) (by omega)
  have hl1 : (30 : ℝ) ≤ I.lwR (k - 1) := by
    have := rat_cast_le_of hl.1; simp only [lwR]; push_cast at this; exact this
  have hl2 : I.lwR (k - 1) ≤ 136 * N + 10 := by
    have := rat_cast_le_of hl.2; simp only [lwR]; push_cast at this; exact this
  set q := (I.umbraR k).q t
  set A' := I.lXR q - I.lXR (ratPoint (I.valley k)) with hA'
  set B' := I.lYR (ratPoint (I.valley k)) - I.lYR q with hB'
  have e : 64 * (I.S : ℝ) ^ 2 * ArtGallery.det q (ratPoint (I.valley k)) s =
      -A' * (I.lYR s - I.lYR (ratPoint (I.valley k))) -
        B' * (I.lXR s - I.lXR (ratPoint (I.valley k))) := by
    rw [det_lXR]; ring
  have h := mul_nonneg h64.le hq
  rw [e] at h
  have hA1 : 15 * (I.S : ℝ) ≤ A' := by rw [hA', qx, vx]; nlinarith
  have hBA : A' - 2000 ≤ B' := by rw [hA', hB', qx, qy, vx, vy, hr]; nlinarith
  have hNp : (0 : ℝ) < N := by linarith
  have he : 2000 ≤ A' / (500 * N) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hB2 : A' * (1 - 1 / (500 * N)) ≤ B' := by
    have : A' * (1 - 1 / (500 * N)) = A' - A' / (500 * N) := by ring
    linarith
  have hd : 0 ≤ I.lXR s - I.lXR (ratPoint (I.valley k)) := by linarith
  have h2 : A' * (I.lYR s - I.lYR (ratPoint (I.valley k))) ≤
      -(A' * (1 - 1 / (500 * N))) * (I.lXR s - I.lXR (ratPoint (I.valley k))) := by
    nlinarith [mul_le_mul_of_nonneg_right hB2 hd]
  have hA0 : 0 < A' := by linarith
  have : A' * (I.lYR s - I.lYR (ratPoint (I.valley k))) ≤
      A' * (-(1 - 1 / (500 * N)) * (I.lXR s - I.lXR (ratPoint (I.valley k)))) := by
    linarith [h2]
  exact le_of_mul_le_mul_left this hA0

end Recv

end Input

end ArtGallery.Sec5.Corridor

end
