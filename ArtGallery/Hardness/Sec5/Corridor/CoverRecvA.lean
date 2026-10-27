module

public import ArtGallery.Hardness.Sec5.Corridor.CoverBase

/-!
# Section 5: corridors — the receiver's view of the umbra (preparation)

For pair `k` and the receiver guard `q = m + (T_τ + (t, 0))/S`, `t ∈ [0, 3/2]`:

* `Good.recv_conds`: the three receiver conditions of `Corridor/Receiver.lean`
  (`z1` left of `q → z'_k`, `z1` and `z'_k` left of `q → v_k`) for real offsets;
* quadrant lemmas: the walls `z0 → nxt` and `z'_k → z1` have the points south-east of `z0`,
  resp. south-west of `z1`, on their inner side (`Good.wall_quadrant`, `Good.edge_quadrant`);
* `det_cone`: a generic sign lemma for a cone of directions at a vertex;
* `Good.recv_cone`: every point `z` of the umbra piece is left of `q → z'_k` and (for `k ≥ 1`)
  left of `q → v_k`;
* `Good.below_valley`: points left of `q → v_k` east of the valley are below a line of slope
  `−999/1000` through `v_k`;
* `Good.AR_neg_of_line`: points below a line of slope `−m` (`1/2 ≤ m ≤ 1`) east of a bound are
  below the axis.
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ}

/-- **Cone lemma.**  At a vertex `o` with an edge towards `b` turning clockwise into the direction
`p − o` (`det o b p < 0`), a point `z` left of `o → b` and left of `o → p` satisfies
`det q a z ≥ det q a o` whenever the direction `a − q` is clockwise of `b − o` and
counter-clockwise of `p − o`. -/
theorem det_cone {q a o b p z : Point} (h1 : ArtGallery.det o b p < 0)
    (h2 : 0 ≤ ArtGallery.det o b z) (h3 : 0 ≤ ArtGallery.det o p z)
    (h4 : 0 ≤ (a.1 - q.1) * (b.2 - o.2) - (a.2 - q.2) * (b.1 - o.1))
    (h5 : (a.1 - q.1) * (p.2 - o.2) - (a.2 - q.2) * (p.1 - o.1) ≤ 0) :
    ArtGallery.det q a o ≤ ArtGallery.det q a z := by
  have key : ArtGallery.det o b p * (ArtGallery.det q a z - ArtGallery.det q a o) =
      -(ArtGallery.det o p z) * ((a.1 - q.1) * (b.2 - o.2) - (a.2 - q.2) * (b.1 - o.1)) +
      ArtGallery.det o b z * ((a.1 - q.1) * (p.2 - o.2) - (a.2 - q.2) * (p.1 - o.1)) := by
    simp only [ArtGallery.det]; ring
  have : ArtGallery.det o b p * (ArtGallery.det q a z - ArtGallery.det q a o) ≤ 0 := by
    rw [key]; nlinarith [mul_nonneg h3 h4, mul_nonneg h2 (neg_nonneg.2 h5)]
  by_contra hc; push Not at hc
  nlinarith

section Recv

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

omit hk in
/-- Local coordinates of the receiver. -/
theorem Good.rl_recv (_hk : k < I.np) (t : ℝ) :
    I.lXR ((I.umbraR k).q t) = 16 * I.S + 8 * (((I.tu k : ℚ) : ℝ) + t) ∧
      I.lYR ((I.umbraR k).q t) = -(16 * I.S) + 8 * ((I.tw k : ℚ) : ℝ) := by
  obtain ⟨-, -, -, -, hSp, -⟩ := hg.S_big
  rw [umbraR_q]
  simp only [place, lXR, lYR, tu, tw]
  constructor <;> field_simp <;> ring

/-- Bounds on the receiver offsets. -/
theorem Good.recv_atoms :
    -50 ≤ ((I.tu k : ℚ) : ℝ) ∧ ((I.tu k : ℚ) : ℝ) ≤ 50 ∧ -50 ≤ ((I.tw k : ℚ) : ℝ) ∧
      ((I.tw k : ℚ) : ℝ) ≤ 50 ∧ I.rwR k = 10 - 8 * (((I.tu k : ℚ) : ℝ) + ((I.tw k : ℚ) : ℝ)) := by
  obtain ⟨u1, u2⟩ := hg.tu_bound hk
  obtain ⟨w1, w2⟩ := hg.tw_bound hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := rat_cast_le_of u1; push_cast at this; exact this
  · have := rat_cast_le_of u2; push_cast at this; exact this
  · have := rat_cast_le_of w1; push_cast at this; exact this
  · have := rat_cast_le_of w2; push_cast at this; exact this
  · simp only [rwR, rwE]; push_cast; ring

omit hg hk in
/-- `det (q t) A B` is affine in the offset `t`. -/
theorem recv_det_affine (A B : Point) (t : ℝ) :
    ArtGallery.det ((I.umbraR k).q t) A B = ArtGallery.det ((I.umbraR k).q 0) A B +
      (2 * t / 3) * (ArtGallery.det ((I.umbraR k).q (3 / 2)) A B -
        ArtGallery.det ((I.umbraR k).q 0) A B) := by
  simp only [CopyPair.q, ArtGallery.det]; ring

omit hg hk in
theorem recv_det_cast (k : ℕ) (u : ℚ) (a b : ℚ × ℚ) :
    ArtGallery.det ((I.umbraR k).q (u : ℝ)) (ratPoint a) (ratPoint b) =
      ((det2 ((I.umbraQ k).q u) a b : ℚ) : ℝ) := by
  rw [umbraR, CopyPair.castR_q, det_ratPoint]

omit hg hk in
/-- A receiver condition proved over `ℚ` at both ends of the receiver holds for real offsets. -/
theorem recv_det_of {a b : ℚ × ℚ} (h : ∀ u : ℚ, 0 ≤ u → u ≤ 3 / 2 → 0 ≤ det2 ((I.umbraQ k).q u) a b)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) :
    0 ≤ ArtGallery.det ((I.umbraR k).q t) (ratPoint a) (ratPoint b) := by
  rw [recv_det_affine]
  have e0 := recv_det_cast (I := I) k 0 a b
  have e1 := recv_det_cast (I := I) k (3 / 2) a b
  push_cast at e0 e1
  rw [e0, e1]
  have h0 : (0 : ℝ) ≤ ((det2 ((I.umbraQ k).q 0) a b : ℚ) : ℝ) := by
    exact_mod_cast h 0 le_rfl (by norm_num)
  have h1 : (0 : ℝ) ≤ ((det2 ((I.umbraQ k).q (3 / 2)) a b : ℚ) : ℝ) := by
    exact_mod_cast h (3 / 2) (by norm_num) le_rfl
  have : 0 ≤ 2 * t / 3 := by positivity
  have : 2 * t / 3 ≤ 1 := by linarith
  nlinarith

/-- **The receiver conditions** (`Corridor/Receiver.lean`) for real offsets. -/
theorem Good.recv_conds {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) :
    0 ≤ ArtGallery.det ((I.umbraR k).q t) (ratPoint (I.zp k)) (ratPoint (I.z1 k)) ∧
      (1 ≤ k → 0 ≤ ArtGallery.det ((I.umbraR k).q t) (ratPoint (I.valley k)) (ratPoint (I.z1 k))) ∧
      (1 ≤ k → 0 ≤ ArtGallery.det ((I.umbraR k).q t) (ratPoint (I.valley k)) (ratPoint (I.zp k))) :=
  ⟨recv_det_of (fun _ h0 h1 => hg.recv_zp hk h0 h1) ht0 ht1,
    fun hk1 => recv_det_of (fun _ h0 h1 => hg.recv_valley_z1 hk hk1 h0 h1) ht0 ht1,
    fun hk1 => recv_det_of (fun _ h0 h1 => hg.recv_valley_zp hk hk1 h0 h1) ht0 ht1⟩

/-- **Quadrant of the left wall**: points south-east of `z0` are on its inner side. -/
theorem Good.wall_quadrant {P : Point} (hx : I.lXR (ratPoint (I.z0 k)) ≤ I.lXR P)
    (hy : I.lYR P ≤ I.lYR (ratPoint (I.z0 k))) :
    0 ≤ ArtGallery.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) P := by
  obtain ⟨-, -, -, -, -, h64⟩ := hg.S_big
  obtain ⟨n1, n2⟩ := hg.rl_nxt hk
  obtain ⟨z0x, z0y⟩ := hg.rl_z0 hk
  obtain ⟨l1, l2, r1, r2, hN, hS, hw⟩ := hg.pairR hk
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw2
  obtain ⟨-, -, hS1, -⟩ := hg.S_big
  have hnx : I.lXR (ratPoint (I.nxt k)) ≤ I.lXR (ratPoint (I.z0 k)) ∧
      I.lYR (ratPoint (I.nxt k)) ≤ I.lYR (ratPoint (I.z0 k)) := by
    rw [z0x, z0y]
    by_cases h : k + 1 < I.np
    · rw [(n1 h).1, (n1 h).2]; constructor <;> linarith
    · rw [(n2 h).1, (n2 h).2]; constructor <;> nlinarith
  refine nonneg_of_mul_nonneg_c h64 ?_
  rw [det_lXR]
  nlinarith [mul_nonneg (sub_nonneg.2 hnx.1) (sub_nonneg.2 hx),
    mul_nonneg (sub_nonneg.2 hnx.2) (sub_nonneg.2 hy)]

/-- **Quadrant of the edge `z'_k → z1`**: points south-west of `z1` are on its inner side. -/
theorem Good.edge_quadrant {P : Point} (hx : I.lXR P ≤ I.lXR (ratPoint (I.z1 k)))
    (hy : I.lYR P ≤ I.lYR (ratPoint (I.z1 k))) :
    0 ≤ ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)) P := by
  obtain ⟨-, -, -, -, -, h64⟩ := hg.S_big
  obtain ⟨z1x, z1y⟩ := hg.rl_z1 hk
  obtain ⟨zx, zy, -, -, -⟩ := hg.rl_zp hk
  rw [abs_le] at zx zy
  refine nonneg_of_mul_nonneg_c h64 ?_
  have e : 64 * (I.S : ℝ) ^ 2 * ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)) P =
      (I.lXR (ratPoint (I.z1 k)) - I.lXR (ratPoint (I.zp k))) *
        (I.lYR P - I.lYR (ratPoint (I.z1 k))) -
      (I.lXR P - I.lXR (ratPoint (I.z1 k))) *
        (I.lYR (ratPoint (I.z1 k)) - I.lYR (ratPoint (I.zp k))) := by
    rw [det_lXR]; ring
  rw [e]
  have a1 : I.lXR (ratPoint (I.z1 k)) - I.lXR (ratPoint (I.zp k)) ≤ 0 := by linarith
  have a2 : 0 ≤ I.lYR (ratPoint (I.z1 k)) - I.lYR (ratPoint (I.zp k)) := by linarith
  nlinarith [mul_nonneg (neg_nonneg.2 a1) (sub_nonneg.2 hy),
    mul_nonneg (sub_nonneg.2 hx) a2]

omit hg hk in
/-- Two points of the axis: `D (Y_a − Y_b) = h (X_a − X_b)`. -/
theorem axis_rel {A B : Point} (hA : I.AR k A = 0) (hB : I.AR k B = 0) :
    ((I.DD k : ℚ) : ℝ) * (I.lYR A - I.lYR B) = ((I.hh k : ℚ) : ℝ) * (I.lXR A - I.lXR B) := by
  simp only [AR] at hA hB; linarith

/-- The axis function as a determinant with the axis vertices `z'_k`, `p_k`. -/
theorem Good.AR_det (P : Point) :
    64 * (I.S : ℝ) ^ 2 * ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.sgPt k)) P *
      ((I.DD k : ℚ) : ℝ) =
      (I.lXR (ratPoint (I.sgPt k)) - I.lXR (ratPoint (I.zp k))) * I.AR k P := by
  have hz := (hg.rl_zp hk).2.2.2.2
  have hp := hg.AR_sgPt hk
  rw [det_lXR]
  simp only [AR] at hz hp ⊢
  linear_combination (I.lXR P - I.lXR (ratPoint (I.sgPt k))) * hz -
    (I.lXR P - I.lXR (ratPoint (I.zp k))) * hp

end Recv

end Input

end ArtGallery.Sec5.Corridor

end
