module

public import ArtGallery.Hardness.Sec5.Corridor.CoverSeg

/-!
# Section 5: corridors — the base guards see the umbra through the entrance

For pair `k` and the base guard `g = (27σ_k/2 + t, 0)` (`t ∈ [0, 3/2]`):

* `Good.base_seg`: if `z` is a point of the umbra piece with `det(g, c0, z) ≥ 0` (on the base
  guard's side of its line through `c0`), the segment `g z` crosses the entrance `d0 c0` at a point
  `w`, and the segment `w z` lies in the corridor region: it runs through the strip pieces of the
  pairs `j ≥ k` and the umbra piece of pair `k` (pointwise, using that `ζ` increases along the
  sight line).

Auxiliary: `Good.umbra_box` (the umbra piece lies within `18 ε` of the apex),
`Good.wall_entrance`, `Good.edge_entrance` (the entrance is on the inner side of the walls).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ}

section Base

variable (hg : I.Good N)
include hg

/-- Points of the entrance in local coordinates. -/
theorem Good.entrance_coords {w : Point} (hw : w ∈ I.entrance) :
    w.1 = I.S ∧ (I.H : ℝ) ≤ w.2 ∧ w.2 ≤ (I.H : ℝ) + 2 * I.rhoR ∧
      I.lXR w = -(8 * I.S) ∧ -(8 * (I.S : ℝ)) ≤ I.lYR w ∧ I.lYR w ≤ -(8 * I.S) + 24 := by
  obtain ⟨μ, h0, h1, rfl⟩ := hw
  have hρ := hg.rhoR_pos
  have hS : (0 : ℝ) < I.S := by exact_mod_cast hg.S_pos
  rw [ratPoint_d0', ratPoint_c0']
  simp only
  refine ⟨by ring, by nlinarith, by nlinarith, by simp only [lXR]; ring, ?_, ?_⟩
  · simp only [lYR]
    have h := mul_nonneg (mul_nonneg hS.le hρ.le) (sub_nonneg.2 h1)
    nlinarith
  · simp only [lYR, rhoR_eq]
    have : 8 * (I.S : ℝ) * (2 * (3 / (2 * I.S))) = 24 := by field_simp; ring
    nlinarith

variable {k : ℕ} (hk : k < I.np)
include hk

/-- The umbra piece lies near the apex. -/
theorem Good.umbra_box {z : Point} (hz : z ∈ hpSet (I.umbraFs k)) :
    (I.rwR k - I.lwR k) / 2 - 18 ≤ I.lXR z ∧ I.lXR z ≤ (I.rwR k - I.lwR k) / 2 + 17 ∧
      (I.lwR k + I.rwR k) / 2 - 17 ≤ I.lYR z ∧ I.lYR z ≤ (I.lwR k + I.rwR k) / 2 - 3 := by
  have hζ := hg.umbra_zeta hk hz
  rw [mem_umbra_iff] at hz
  obtain ⟨hA, -, hy, -, hx, -, -⟩ := hz
  obtain ⟨zx, -, -, -, -⟩ := hg.rl_zp hk
  obtain ⟨-, z1y⟩ := hg.rl_z1 hk
  obtain ⟨l1, l2, r1, r2, hN, hS, hw⟩ := hg.pairR hk
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at zx hw2
  have hX1 : (I.rwR k - I.lwR k) / 2 - 18 ≤ I.lXR z := by
    by_contra hc
    push Not at hc
    have := hg.AR_neg_of_zeta hk (Z := I.lwR k) (Xmax := (I.rwR k - I.lwR k) / 2 - 18)
      (by rw [abs_le]; constructor <;> linarith) hζ hc.le (by linarith)
    linarith
  have hX2 : I.lXR z ≤ (I.rwR k - I.lwR k) / 2 + 17 := by linarith
  refine ⟨hX1, hX2, ?_, by rw [z1y] at hy; exact hy⟩
  by_contra hc
  push Not at hc
  have := hg.AR_neg_of hk (z := z) (by rw [abs_le]; constructor <;> linarith) (by linarith)
  linarith

/-- The entrance is on the inner side of every left wall. -/
theorem Good.wall_entrance {w : Point} (hw : w ∈ I.entrance) :
    0 ≤ ArtGallery.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) w := by
  obtain ⟨-, -, -, hx, hy1, hy2⟩ := hg.entrance_coords hw
  obtain ⟨w1, w2⟩ := hg.wall_det hk w
  obtain ⟨l1, l2, r1, r2, hN, hS, hww⟩ := hg.pairR hk
  obtain ⟨-, -, hS1, -, hSp, h64⟩ := hg.S_big
  refine nonneg_of_mul_nonneg_right ?_ h64
  rw [mul_comm]
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw2
  by_cases h : k + 1 < I.np
  · rw [mul_comm, w1 h, hx]; nlinarith
  · rw [mul_comm, w2 h, hx]
    have e : 8 * (I.S : ℝ) * (I.lwR k - (I.lYR w - -(8 * I.S))) -
        ((I.rwR k - I.lwR k) / 2 - 3) * (I.lYR w - ((I.lwR k + I.rwR k) / 2 - 3)) -
        (-(8 * I.S) - ((I.rwR k - I.lwR k) / 2 - 3)) * (24 - ((I.lwR k + I.rwR k) / 2 - 3)) =
        (8 * I.S + ((I.rwR k - I.lwR k) / 2 - 3)) * (24 - (I.lYR w + 8 * I.S)) := by ring
    rw [e]
    exact mul_nonneg (by linarith) (by linarith)

/-- The entrance is on the inner side of the edge `z'_k → z1`. -/
theorem Good.edge_entrance {w : Point} (hw : w ∈ I.entrance) :
    0 ≤ ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)) w := by
  obtain ⟨-, -, -, hx, hy1, hy2⟩ := hg.entrance_coords hw
  have e := hg.edge_det hk w
  obtain ⟨z1x, z1y⟩ := hg.rl_z1 hk
  obtain ⟨zx, zy, zξ1, zξ2, -⟩ := hg.rl_zp hk
  obtain ⟨l1, l2, r1, r2, hN, hS, hww⟩ := hg.pairR hk
  obtain ⟨-, -, hS1, -, hSp, h64⟩ := hg.S_big
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at zx zy hw2
  refine nonneg_of_mul_nonneg_c h64 ?_
  rw [e, z1x, hx]
  set X' := I.lXR (ratPoint (I.zp k))
  set ξ' := I.lXR (ratPoint (I.zp k)) + I.lYR (ratPoint (I.zp k))
  have a1 : 0 ≤ ((I.rwR k - I.lwR k) / 2 + 3 - X') * ((-(8 * I.S) + I.lYR w) - ξ') := by
    apply mul_nonneg_of_nonpos_of_nonpos <;> linarith
  have a2 : (-(8 * I.S) - X') * (I.rwR k - ξ') ≤ 8 * I.S + 1000 * N := by
    have b1 : |-(8 * I.S) - X'| ≤ 8 * I.S + 500 * N := by rw [abs_le]; constructor <;> linarith
    have b2 : |I.rwR k - ξ'| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have := abs_mul (-(8 * I.S) - X') (I.rwR k - ξ')
    have b3 := mul_le_mul b1 b2 (abs_nonneg _) (by linarith)
    have := le_abs_self ((-(8 * I.S) - X') * (I.rwR k - ξ'))
    nlinarith
  have a3 : ((I.rwR k - I.lwR k) / 2 + 3 - X') * ((-(8 * I.S) + I.lYR w) - ξ') ≥
      12 * (8 * I.S - 1000 * N) := by
    have c1 : 12 ≤ -((I.rwR k - I.lwR k) / 2 + 3 - X') := by linarith
    have c2 : 8 * I.S - 1000 * N ≤ -((-(8 * I.S) + I.lYR w) - ξ') := by nlinarith
    nlinarith
  nlinarith

/-- Monotonicity of the coordinates along the sight line of a base guard towards a point near
the corridor's middle. -/
theorem Good.base_mono {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) {z s : Point}
    (hzx : |I.lXR z| ≤ 456 * N) (hzy : |I.lYR z| ≤ 456 * N)
    (hs : s ∈ ArtGallery.segment ((I.umbraR k).p t) z) :
    I.lXR s ≤ I.lXR z ∧ I.lYR s ≤ I.lYR z ∧ I.lYR s - I.lXR s ≤ I.lYR z - I.lXR z := by
  obtain ⟨hg0, hg1, hg2, hgx⟩ := hg.base_x hk ht0 ht1
  obtain ⟨hN, hS, hS1, -, hSp, -⟩ := hg.S_big
  have hH : (I.S : ℝ) + 1 ≤ I.H := hg.scaleR.hH1
  obtain ⟨ν, hν0, hν1, rfl⟩ := hs
  set g := (I.umbraR k).p t
  rw [abs_le] at hzx hzy
  have hgx' : g.1 ≤ 14 * N := by rw [hgx]; linarith
  have ex : I.lXR z - I.lXR g = 8 * I.S * (z.1 - g.1) := by simp only [lXR]; ring
  have ey : I.lYR z - I.lYR g = 8 * I.S * (z.2 - g.2) := by simp only [lYR]; ring
  have hz1 : z.1 = I.S + 1 + I.lXR z / (8 * I.S) := by simp only [lXR]; field_simp; ring
  have hz2 : z.2 = I.H + 1 + I.lYR z / (8 * I.S) := by simp only [lYR]; field_simp; ring
  have hS8 : (0 : ℝ) < 8 * I.S := by linarith
  have a1 : -(1 / 2 : ℝ) ≤ I.lXR z / (8 * I.S) := by rw [le_div_iff₀ hS8]; nlinarith
  have a2 : I.lXR z / (8 * I.S) ≤ 1 / 2 := by rw [div_le_iff₀ hS8]; nlinarith
  have a3 : -(1 / 2 : ℝ) ≤ I.lYR z / (8 * I.S) := by rw [le_div_iff₀ hS8]; nlinarith
  have d1 : 0 ≤ z.1 - g.1 := by rw [hz1]; nlinarith
  have d2 : 0 ≤ z.2 - g.2 := by rw [hz2, hg2]; nlinarith
  have d3 : 0 ≤ (z.2 - g.2) - (z.1 - g.1) := by rw [hz1, hz2, hg2]; nlinarith
  have f : ∀ c : ℝ, 0 ≤ c → (1 - ν) * (8 * I.S * c) ≥ 0 := fun c hc =>
    mul_nonneg (by linarith) (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · have e : I.lXR z - I.lXR (g.1 + ν * (z.1 - g.1), g.2 + ν * (z.2 - g.2)) =
        (1 - ν) * (8 * I.S * (z.1 - g.1)) := by simp only [lXR]; ring
    linarith [f _ d1]
  · have e : I.lYR z - I.lYR (g.1 + ν * (z.1 - g.1), g.2 + ν * (z.2 - g.2)) =
        (1 - ν) * (8 * I.S * (z.2 - g.2)) := by simp only [lYR]; ring
    linarith [f _ d2]
  · have e : (I.lYR z - I.lXR z) - (I.lYR (g.1 + ν * (z.1 - g.1), g.2 + ν * (z.2 - g.2)) -
        I.lXR (g.1 + ν * (z.1 - g.1), g.2 + ν * (z.2 - g.2))) =
        (1 - ν) * (8 * I.S * ((z.2 - g.2) - (z.1 - g.1))) := by simp only [lYR, lXR]; ring
    linarith [f _ d3]

/-- The sight line of the base guard towards a point of the umbra piece in its band crosses the
entrance. -/
theorem Good.base_entrance {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) {z : Point}
    (hz : z ∈ hpSet (I.umbraFs k))
    (hc0 : 0 ≤ ArtGallery.det ((I.umbraR k).p t) (ratPoint (c0 I.S I.H)) z) :
    ∃ w ∈ I.entrance, w ∈ ArtGallery.segment ((I.umbraR k).p t) z := by
  obtain ⟨hg0, hg1, hg2, hgx⟩ := hg.base_x hk ht0 ht1
  obtain ⟨zX1, zX2, zY1, zY2⟩ := hg.umbra_box hk hz
  have hζz := hg.umbra_zeta hk hz
  obtain ⟨l1, l2, r1, r2, hN, hS, hww⟩ := hg.pairR hk
  obtain ⟨-, -, hS1, -, hSp, h64⟩ := hg.S_big
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw2
  have hzw : |I.lXR z| ≤ 456 * N := by rw [abs_le]; constructor <;> linarith
  have hd0 := hg.base_d0_nonpos hk ht0 ht1 hzw (by linarith)
  set g := (I.umbraR k).p t with hgdef
  have hS8 : (0 : ℝ) < 8 * I.S := by linarith
  have hz1 : z.1 = I.S + 1 + I.lXR z / (8 * I.S) := by simp only [lXR]; field_simp; ring
  have hzx : (I.S : ℝ) + 1 / 2 ≤ z.1 := by
    rw [hz1]
    have : -(1 / 2 : ℝ) ≤ I.lXR z / (8 * I.S) := by rw [le_div_iff₀ hS8]; nlinarith
    linarith
  have hgS : g.1 + 1 ≤ I.S := by rw [hgx]; nlinarith
  obtain ⟨w, hwseg, hwx⟩ := exists_mem_segment_ev_eq ⟨1, 0, 0⟩ (g := g) (z := z) (c := I.S)
    (by simp only [Aff.ev]; linarith) (by simp only [Aff.ev]; linarith)
  simp only [Aff.ev, one_mul, zero_mul, add_zero] at hwx
  refine ⟨w, ?_, hwseg⟩
  obtain ⟨μ, hμ0, hμ1, hwdef⟩ := hwseg
  have hdet : ∀ a : Point, ArtGallery.det g a w = μ * ArtGallery.det g a z := by
    intro a; rw [hwdef]; simp only [ArtGallery.det]; ring
  have hρ := hg.rhoR_pos
  have hgx' : 0 < (I.S : ℝ) - g.1 := by linarith
  have e1 : ArtGallery.det g (ratPoint (c0 I.S I.H)) w = ((I.S : ℝ) - g.1) * (w.2 - I.H) := by
    rw [ratPoint_c0']; simp only [ArtGallery.det, hg2, hwx]; ring
  have e2 : ArtGallery.det g (ratPoint (d0 I.S I.H)) w =
      ((I.S : ℝ) - g.1) * (w.2 - (I.H + 2 * I.rhoR)) := by
    rw [ratPoint_d0']; simp only [ArtGallery.det, hg2, hwx]; ring
  have hy1 : (I.H : ℝ) ≤ w.2 := by
    have := nonneg_of_mul_nonneg_c hgx' (by rw [← e1, hdet]; exact mul_nonneg hμ0 hc0)
    linarith
  have hy2 : w.2 ≤ (I.H : ℝ) + 2 * I.rhoR := by
    have h := hdet (ratPoint (d0 I.S I.H))
    rw [e2] at h
    have : ((I.S : ℝ) - g.1) * (w.2 - (I.H + 2 * I.rhoR)) ≤ 0 := by
      rw [h]; exact mul_nonpos_of_nonneg_of_nonpos hμ0 hd0
    by_contra hc; push Not at hc
    have := mul_pos hgx' (show 0 < w.2 - (I.H + 2 * I.rhoR) by linarith)
    linarith
  refine ⟨((I.H : ℝ) + 2 * I.rhoR - w.2) / (2 * I.rhoR), by positivity,
    by rw [div_le_one (by positivity)]; linarith, ?_⟩
  rw [ratPoint_d0', ratPoint_c0']
  ext
  · simp only; rw [hwx]; ring
  · simp only; field_simp; ring

omit hk in
/-- A point of the strip of a pair `j` west of `k`, below `ζ = ℓ_k`, inside the left wall of `j`,
is in the strip piece of `j`. -/
theorem Good.west_point (_hk : k < I.np) {j : ℕ} (hkj : k < j) (hj : j < I.np) {s : Point}
    (hj1 : I.lXR (ratPoint (I.nxt j)) ≤ I.lXR s) (hj2 : I.lXR s ≤ I.lXR (ratPoint (I.sgPt j)))
    (hsH : -(8 * (I.S : ℝ)) ≤ I.lYR s) (hsζ : I.lYR s - I.lXR s ≤ I.lwR k)
    (hlast : ¬ j + 1 < I.np → 0 ≤ ArtGallery.det (ratPoint (I.z0 j)) (ratPoint (I.nxt j)) s) :
    s ∈ I.poly.filled := by
  refine hg.strip_subset hj ?_
  rw [mem_strip_iff]
  refine ⟨hj2, hj1, hsH, ?_, ?_⟩
  · have hj1' : 1 ≤ j := by omega
    obtain ⟨px, -⟩ := hg.rl_sgPt hj hj1'
    have hlm := hg.lw_mono (show k ≤ j - 1 by omega) (show j - 1 < I.np by omega)
    have hls := hg.lw_succ (j := j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega] at hls
    obtain ⟨-, -, -, e4, -⟩ := hg.rl_strip_ends hj
    exact (hg.AR_neg_of_zeta hj (Z := I.lwR (j - 1)) (Xmax := I.lXR (ratPoint (I.sgPt j)))
      (e4 hj1') (by linarith) hj2 (by rw [px]; linarith)).le
  · by_cases h : j + 1 < I.np
    · obtain ⟨w1, -⟩ := hg.wall_det hj s
      have hlm := hg.lw_mono hkj.le hj
      obtain ⟨-, -, -, -, -, h64⟩ := hg.S_big
      refine nonneg_of_mul_nonneg_c h64 ?_
      rw [w1 h]; nlinarith
    · exact hlast h

/-- A point of the sight segment from the entrance to the umbra lies in the corridor region. -/
theorem Good.base_point {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) {z w s : Point}
    (hz : z ∈ hpSet (I.umbraFs k)) (hw : w ∈ I.entrance)
    (hwg : w ∈ ArtGallery.segment ((I.umbraR k).p t) z) (hs : s ∈ ArtGallery.segment w z) :
    s ∈ I.poly.filled := by
  obtain ⟨zX1, zX2, zY1, zY2⟩ := hg.umbra_box hk hz
  have hζz := hg.umbra_zeta hk hz
  have hzmem := hz
  rw [mem_umbra_iff] at hzmem
  obtain ⟨zA, zE, zY, zW, zX, zN, zH⟩ := hzmem
  obtain ⟨l1, l2, r1, r2, hN, hS, hww⟩ := hg.pairR hk
  obtain ⟨-, -, hS1, -, hSp, h64⟩ := hg.S_big
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw2
  obtain ⟨-, wy1, -, wx, wly1, wly2⟩ := hg.entrance_coords hw
  have hsgz : s ∈ ArtGallery.segment ((I.umbraR k).p t) z :=
    Geometry.segment_subset_of_convex (Geometry.segment_convex _ z) hwg
      (Geometry.right_mem_segment _ z) hs
  obtain ⟨hlx, hly, hlζ⟩ := hg.base_mono hk ht0 ht1 (by rw [abs_le]; constructor <;> linarith)
    (by rw [abs_le]; constructor <;> linarith) hsgz
  have hsH : -(8 * (I.S : ℝ)) ≤ I.lYR s := by
    have := (Aff.ge_ev_of_segment (I.cA 0 1 0) hs (c := -(8 * (I.S : ℝ)))
      (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith))
    rw [ev_cA] at this; linarith
  have hsS : -(8 * (I.S : ℝ)) ≤ I.lXR s := by
    have := (Aff.ge_ev_of_segment (I.cA 1 0 0) hs (c := -(8 * (I.S : ℝ)))
      (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith))
    rw [ev_cA] at this; linarith
  have hsW : 0 ≤ ArtGallery.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) s := by
    have := Aff.ge_ev_of_segment (Aff.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k))) hs (c := 0)
      (by rw [Aff.ev_det]; exact hg.wall_entrance hk hw) (by rw [Aff.ev_det]; exact zW)
    rwa [Aff.ev_det] at this
  have hsE : 0 ≤ ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)) s := by
    have := Aff.ge_ev_of_segment (Aff.det (ratPoint (I.zp k)) (ratPoint (I.z1 k))) hs (c := 0)
      (by rw [Aff.ev_det]; exact hg.edge_entrance hk hw) (by rw [Aff.ev_det]; exact zE)
    rwa [Aff.ev_det] at this
  have hzpp : I.lXR (ratPoint (I.zp k)) < I.lXR (ratPoint (I.sgPt k)) := by
    rw [lXR_ratPoint, lXR_ratPoint]
    exact_mod_cast (fst_lt_iff hg).1 (hg.zp_lt_sgPt hk)
  obtain ⟨j, hkj, hj, hj1, hj2⟩ := hg.strip_west hk hsS (by linarith)
  rcases hkj.lt_or_eq with hkj | rfl
  · -- a strip of a pair to the west
    refine hg.west_point hk hkj hj hj1 hj2 hsH (hlζ.trans hζz) fun h => ?_
    have hzW : 0 ≤ ArtGallery.det (ratPoint (I.z0 j)) (ratPoint (I.nxt j)) z := by
      have hlm' := hg.lw_succ (j := k) (by omega)
      have hlm'' := hg.lw_mono (show k + 1 ≤ j by omega) hj
      exact (hg.wall_of_window hj (by rw [abs_le]; constructor <;> linarith)
        (by rw [abs_le]; constructor <;> linarith) (by linarith)).le
    have := Aff.ge_ev_of_segment (Aff.det (ratPoint (I.z0 j)) (ratPoint (I.nxt j))) hs
      (c := 0) (by rw [Aff.ev_det]; exact hg.wall_entrance hj hw)
      (by rw [Aff.ev_det]; exact hzW)
    rwa [Aff.ev_det] at this
  · -- the strip of pair `k`: below the axis, or in the umbra
    rcases le_or_gt (I.AR k s) 0 with hA | hA
    · refine hg.strip_subset hk ?_
      rw [mem_strip_iff]
      exact ⟨hj2, hj1, hsH, hA, hsW⟩
    · refine hg.umbra_subset hk ?_
      rw [mem_umbra_iff]
      exact ⟨hA.le, hsE, hly.trans zY, hsW, hlx.trans zX, hj1, hsH⟩

/-- **The base guard sees the umbra through the entrance.** -/
theorem Good.base_seg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) {z : Point}
    (hz : z ∈ hpSet (I.umbraFs k))
    (hc0 : 0 ≤ ArtGallery.det ((I.umbraR k).p t) (ratPoint (c0 I.S I.H)) z) :
    ∃ w ∈ I.entrance, w ∈ ArtGallery.segment ((I.umbraR k).p t) z ∧
      ArtGallery.segment w z ⊆ I.poly.filled := by
  obtain ⟨w, hw, hwg⟩ := hg.base_entrance hk ht0 ht1 hz hc0
  exact ⟨w, hw, hwg, fun s hs => hg.base_point hk ht0 ht1 hz hw hwg hs⟩

end Base

end Input

end ArtGallery.Sec5.Corridor

end
