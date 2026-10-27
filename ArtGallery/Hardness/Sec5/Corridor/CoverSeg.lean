module

public import ArtGallery.Hardness.Sec5.Corridor.CoverUmbra

/-!
# Section 5: corridors — tools for the sight segments of the copy guards

* **Strips** (`Good.strip_west`, `Good.strip_east`): the strips of the pairs tile the corridor:
  every abscissa between `x = S` and `p_k` lies in the strip of some pair `j ≥ k`, every abscissa
  between `nxt_k` and `x = S + 2` in the strip of some pair `j ≤ k`.
* **Bands** (`Good.base_d0_nonpos`, `Good.base_c0_nonneg`, `Good.recv_c1_nonpos`,
  `Good.recv_d1_nonneg`): signs of the lines through the doors for points of the window, in terms
  of `ζ = lY − lX` and `ξ = lY + lX` (from the slab lemmas `band_c0`, … of `Slabs.lean`).
* `Good.AR_neg_of_zeta`: points below a line of slope one, west of a bound, are below an axis.
* `Good.umbra_zeta`: points of the umbra piece have `ζ ≤ ℓ`.
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ}

section Seg

variable (hg : I.Good N)
include hg

/-! ## Index facts -/

theorem Good.lw_succ {j : ℕ} (hj : j + 1 < I.np) : I.lwR j + 108 ≤ I.lwR (j + 1) := by
  have := rat_cast_le_of (hg.lwE_succ hj); simp only [lwR]; push_cast at this; exact this

theorem Good.rw_succ {j : ℕ} (hj : j + 1 < I.np) : I.rwR (j + 1) = I.rwR j - 108 := by
  simp only [rwR]; rw [hg.rwE_succ hj]; push_cast; ring

theorem Good.lw_mono {j j' : ℕ} (hjj : j ≤ j') (hj' : j' < I.np) : I.lwR j ≤ I.lwR j' := by
  induction j' with
  | zero => obtain rfl : j = 0 := by omega
            exact le_rfl
  | succ j' ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hjj) with h | h
    · have := hg.lw_succ hj'
      linarith [ih (by omega) (by omega)]
    · rw [h]

/-- Consecutive strips share their boundary line: `x(p_{j+1}) = x(nxt_j)`. -/
theorem Good.sgPt_succ_nxt {j : ℕ} (hj : j + 1 < I.np) :
    I.lXR (ratPoint (I.sgPt (j + 1))) = I.lXR (ratPoint (I.nxt j)) := by
  rw [(hg.rl_sgPt hj (by omega)).1, ((hg.rl_nxt (by omega : j < I.np)).1 hj).1,
    hg.rw_succ hj, show j + 1 - 1 = j by omega]
  ring

/-- **Strips to the west.** -/
theorem Good.strip_west {k : ℕ} (hk : k < I.np) {x : ℝ} (h1 : -(8 * (I.S : ℝ)) ≤ x)
    (h2 : x ≤ I.lXR (ratPoint (I.sgPt k))) :
    ∃ j, k ≤ j ∧ j < I.np ∧ I.lXR (ratPoint (I.nxt j)) ≤ x ∧
      x ≤ I.lXR (ratPoint (I.sgPt j)) := by
  induction hm : I.np - k generalizing k with
  | zero => omega
  | succ m ih =>
    by_cases hx : I.lXR (ratPoint (I.nxt k)) ≤ x
    · exact ⟨k, le_rfl, hk, hx, h2⟩
    · push Not at hx
      by_cases hk1 : k + 1 < I.np
      · obtain ⟨j, hj1, hj2, hj3, hj4⟩ := ih hk1 (by rw [hg.sgPt_succ_nxt hk1]; exact hx.le)
          (by omega)
        exact ⟨j, by omega, hj2, hj3, hj4⟩
      · have := ((hg.rl_nxt hk).2 hk1).1
        linarith

/-- **Strips to the east.** -/
theorem Good.strip_east {k : ℕ} (hk : k < I.np) {x : ℝ} (h1 : x ≤ 8 * (I.S : ℝ))
    (h2 : I.lXR (ratPoint (I.nxt k)) ≤ x) :
    ∃ j, j ≤ k ∧ I.lXR (ratPoint (I.nxt j)) ≤ x ∧ x ≤ I.lXR (ratPoint (I.sgPt j)) := by
  induction k with
  | zero =>
    refine ⟨0, le_rfl, h2, ?_⟩
    rw [rl_sgPt_zero]; exact h1
  | succ k ih =>
    by_cases hx : x ≤ I.lXR (ratPoint (I.sgPt (k + 1)))
    · exact ⟨k + 1, le_rfl, h2, hx⟩
    · push Not at hx
      rw [hg.sgPt_succ_nxt hk] at hx
      obtain ⟨j, hj1, hj2, hj3⟩ := ih (by omega) hx.le
      exact ⟨j, by omega, hj2, hj3⟩

/-! ## Bands of the copy guards -/

variable {k : ℕ} (hk : k < I.np)
include hk

/-- The base guard of pair `k` at offset `t`. -/
theorem Good.base_x {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) :
    0 ≤ ((I.umbraR k).p t).1 ∧ 27 * ((I.sigma k : ℕ) : ℝ) / 2 + t ≤ 14 * N ∧
      ((I.umbraR k).p t).2 = 0 ∧ ((I.umbraR k).p t).1 = 27 * ((I.sigma k : ℕ) : ℝ) / 2 + t := by
  rw [umbraR_p]
  have := hg.slot_le k hk
  have h' := rat_cast_le_of this; push_cast at h'
  refine ⟨by positivity, by linarith, rfl, rfl⟩

/-- Points of the window below `ζ = ℓ + 1` are on the right of (below) the line `g d0`. -/
theorem Good.base_d0_nonpos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) {z : Point}
    (hX : |I.lXR z| ≤ 456 * N) (hζ : I.lYR z - I.lXR z ≤ I.lwR k + 1) :
    ArtGallery.det ((I.umbraR k).p t) (ratPoint (d0 I.S I.H)) z ≤ 0 := by
  obtain ⟨hp0, hp1, -, hpx⟩ := hg.base_x hk ht0 ht1
  have hsc := hg.scaleR
  have hS := hsc.S_pos
  have hxS : 27 * ((I.sigma k : ℕ) : ℝ) / 2 + t < I.S := by
    have := hsc.hS; have := hsc.two_le; nlinarith
  have hX' : |z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1| ≤ 57 * N / I.S := by
    have e : z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1 = I.lXR z / (8 * I.S) := by
      simp only [Oc, lXR]; field_simp
    have h8 : (0 : ℝ) < 8 * I.S := by linarith
    rw [e, abs_div, abs_of_pos h8, div_le_div_iff₀ h8 hS]
    have := mul_le_mul_of_nonneg_right hX hS.le
    linarith
  rw [umbraR_p, ratPoint_d0, det_eq_det2, det2_eq_lineZeta (Oc (I.S : ℝ) (I.H : ℝ)) _ _ _
    (by simp [d0]; linarith)]
  have b := band_d0 hsc ht0 hp1 hX'
  rw [abs_lt] at b
  have hz := zeta_lXR (I := I) z
  have hZ := hg.Zs_eps k (2 + 2 * t / 3)
  have he := hg.eps_eps
  have hd : (0 : ℝ) ≤ (d0 (I.S : ℝ) (I.H : ℝ)).1 - (27 * ((I.sigma k : ℕ) : ℝ) / 2 + t, (0 : ℝ)).1 := by
    simp [d0]; linarith
  refine mul_nonpos_of_nonneg_of_nonpos hd ?_
  have h8 : (0 : ℝ) < 8 * I.S := by positivity
  have : 8 * (I.S : ℝ) * (zetaOf (Oc (I.S : ℝ) (I.H : ℝ)) z -
      lineZeta (Oc (I.S : ℝ) (I.H : ℝ)) (27 * ((I.sigma k : ℕ) : ℝ) / 2 + t, 0)
        (d0 (I.S : ℝ) (I.H : ℝ)) (z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1)) ≤ 0 := by
    have hb : 8 * (I.S : ℝ) * (Zs (I.S : ℝ) (I.H : ℝ) (I.sigma k) (2 + 2 * t / 3) -
        eps (I.S : ℝ) / 10) < 8 * (I.S : ℝ) * lineZeta (Oc (I.S : ℝ) (I.H : ℝ))
          (27 * ((I.sigma k : ℕ) : ℝ) / 2 + t, 0) (d0 (I.S : ℝ) (I.H : ℝ))
          (z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1) := mul_lt_mul_of_pos_left (by linarith) h8
    rw [mul_sub, hz]
    rw [mul_sub, hZ, show 8 * (I.S : ℝ) * (eps (I.S : ℝ) / 10) = 1 / 10 by rw [← he]; ring] at hb
    simp only [lwR] at hζ
    linarith
  nlinarith

/-- Points of the window above `ζ = ℓ − 9` are on the left of (above) the line `g c0`. -/
theorem Good.base_c0_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) {z : Point}
    (hX : |I.lXR z| ≤ 456 * N) (hζ : I.lwR k - 9 ≤ I.lYR z - I.lXR z) :
    0 ≤ ArtGallery.det ((I.umbraR k).p t) (ratPoint (c0 I.S I.H)) z := by
  obtain ⟨hp0, hp1, -, hpx⟩ := hg.base_x hk ht0 ht1
  have hsc := hg.scaleR
  have hS := hsc.S_pos
  have hxS : 27 * ((I.sigma k : ℕ) : ℝ) / 2 + t < I.S := by
    have := hsc.hS; have := hsc.two_le; nlinarith
  have hX' : |z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1| ≤ 57 * N / I.S := by
    have e : z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1 = I.lXR z / (8 * I.S) := by
      simp only [Oc, lXR]; field_simp
    have h8 : (0 : ℝ) < 8 * I.S := by linarith
    rw [e, abs_div, abs_of_pos h8, div_le_div_iff₀ h8 hS]
    have := mul_le_mul_of_nonneg_right hX hS.le
    linarith
  rw [umbraR_p, ratPoint_c0, det_eq_det2, det2_eq_lineZeta (Oc (I.S : ℝ) (I.H : ℝ)) _ _ _
    (by simp [c0]; linarith)]
  have b := band_c0 hsc ht0 hp1 hX'
  rw [abs_lt] at b
  have hz := zeta_lXR (I := I) z
  have hZ := hg.Zs_eps k (2 * t / 3)
  have he := hg.eps_eps
  have hd : (0 : ℝ) ≤ (c0 (I.S : ℝ) (I.H : ℝ)).1 - (27 * ((I.sigma k : ℕ) : ℝ) / 2 + t, (0 : ℝ)).1 := by
    simp [c0]; linarith
  refine mul_nonneg hd ?_
  have h8 : (0 : ℝ) < 8 * I.S := by positivity
  have : 0 ≤ 8 * (I.S : ℝ) * (zetaOf (Oc (I.S : ℝ) (I.H : ℝ)) z -
      lineZeta (Oc (I.S : ℝ) (I.H : ℝ)) (27 * ((I.sigma k : ℕ) : ℝ) / 2 + t, 0)
        (c0 (I.S : ℝ) (I.H : ℝ)) (z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1)) := by
    have hb : 8 * (I.S : ℝ) * lineZeta (Oc (I.S : ℝ) (I.H : ℝ))
          (27 * ((I.sigma k : ℕ) : ℝ) / 2 + t, 0) (c0 (I.S : ℝ) (I.H : ℝ))
          (z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1) < 8 * (I.S : ℝ) *
        (Zs (I.S : ℝ) (I.H : ℝ) (I.sigma k) (2 * t / 3) + eps (I.S : ℝ) / 10) :=
      mul_lt_mul_of_pos_left (by linarith) h8
    rw [mul_sub, hz]
    rw [mul_add, hZ, show 8 * (I.S : ℝ) * (eps (I.S : ℝ) / 10) = 1 / 10 by rw [← he]; ring] at hb
    simp only [lwR] at hζ
    linarith
  nlinarith

omit hg hk in
/-- The receiver of pair `k` at offset `t`. -/
theorem Good.recv_q (_hg : I.Good N) (_hk : k < I.np) {t : ℝ} :
    (I.umbraR k).q t = place (I.S : ℝ) (I.H : ℝ) ((ratPoint (I.Tt (I.tau k))).1 + t,
      (ratPoint (I.Tt (I.tau k))).2) := by
  rw [umbraR_q]; rfl

/-- Points of the window above `ξ = r − 9` are on the left of (above) the line `q c1`. -/
theorem Good.recv_c1_nonpos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) {z : Point}
    (hX : |I.lXR z| ≤ 456 * N) (hξ : I.rwR k - 9 ≤ I.lYR z + I.lXR z) :
    ArtGallery.det ((I.umbraR k).q t) (ratPoint (c1 I.S I.H)) z ≤ 0 := by
  have hr := hg.recvHyp hk ht0 ht1
  have hsc := hg.scaleR
  have hS := hsc.S_pos
  have hX' : |z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1| ≤ 57 * N / I.S := by
    have e : z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1 = I.lXR z / (8 * I.S) := by
      simp only [Oc, lXR]; field_simp
    have h8 : (0 : ℝ) < 8 * I.S := by linarith
    rw [e, abs_div, abs_of_pos h8, div_le_div_iff₀ h8 hS]
    have := mul_le_mul_of_nonneg_right hX hS.le
    linarith
  have hq : c1 (I.S : ℝ) (I.H : ℝ) - 0 = c1 (I.S : ℝ) (I.H : ℝ) := by simp
  have hu := hr.hx1
  have hcq : (c1 (I.S : ℝ) (I.H : ℝ)).1 -
      (place (I.S : ℝ) (I.H : ℝ) ((ratPoint (I.Tt (I.tau k))).1 + t,
        (ratPoint (I.Tt (I.tau k))).2)).1 < 0 := by
    simp only [c1, place]
    have : -(52 : ℝ) / I.S < ((ratPoint (I.Tt (I.tau k))).1 + t) / I.S := by
      rw [div_lt_div_iff_of_pos_right hS]; linarith
    have h52 : (52 : ℝ) / I.S < 1 := by
      rw [div_lt_one hS]; have := hsc.S_ge; linarith
    have : -(52 : ℝ) / I.S = -((52 : ℝ) / I.S) := by ring
    linarith
  rw [hg.recv_q hk, ratPoint_c1, det_eq_det2, det2_eq_lineXi (Oc (I.S : ℝ) (I.H : ℝ)) _ _ _
    hcq.ne]
  have b := band_c1 hsc hr hX'
  rw [abs_lt] at b
  have hz := xi_lXR (I := I) z
  have hZ := hg.Xis_eps hk (1 - 2 * t / 3)
  have he := hg.eps_eps
  refine mul_nonpos_of_nonpos_of_nonneg hcq.le ?_
  have h8 : (0 : ℝ) < 8 * I.S := by positivity
  have : 0 ≤ 8 * (I.S : ℝ) * (xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z -
      lineXi (Oc (I.S : ℝ) (I.H : ℝ)) (place (I.S : ℝ) (I.H : ℝ)
        ((ratPoint (I.Tt (I.tau k))).1 + t, (ratPoint (I.Tt (I.tau k))).2))
        (c1 (I.S : ℝ) (I.H : ℝ)) (z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1)) := by
    have hb : 8 * (I.S : ℝ) * lineXi (Oc (I.S : ℝ) (I.H : ℝ)) (place (I.S : ℝ) (I.H : ℝ)
        ((ratPoint (I.Tt (I.tau k))).1 + t, (ratPoint (I.Tt (I.tau k))).2))
          (c1 (I.S : ℝ) (I.H : ℝ)) (z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1) < 8 * (I.S : ℝ) *
        (Xis (I.S : ℝ) (ratPoint I.T0) (I.tau k) (1 - 2 * t / 3) + eps (I.S : ℝ) / 4) :=
      mul_lt_mul_of_pos_left (by linarith) h8
    rw [mul_sub, hz]
    rw [mul_add, hZ, show 8 * (I.S : ℝ) * (eps (I.S : ℝ) / 4) = 1 / 4 by rw [← he]; ring] at hb
    simp only [rwR] at hξ
    linarith
  nlinarith

/-- Points of the window below `ξ = r + 3/2` are on the right of (below) the line `q d1`. -/
theorem Good.recv_d1_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) {z : Point}
    (hX : |I.lXR z| ≤ 456 * N) (hξ : I.lYR z + I.lXR z ≤ I.rwR k + 3 / 2) :
    0 ≤ ArtGallery.det ((I.umbraR k).q t) (ratPoint (d1 I.S I.H)) z := by
  have hr := hg.recvHyp hk ht0 ht1
  have hsc := hg.scaleR
  have hS := hsc.S_pos
  have hX' : |z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1| ≤ 57 * N / I.S := by
    have e : z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1 = I.lXR z / (8 * I.S) := by
      simp only [Oc, lXR]; field_simp
    have h8 : (0 : ℝ) < 8 * I.S := by linarith
    rw [e, abs_div, abs_of_pos h8, div_le_div_iff₀ h8 hS]
    have := mul_le_mul_of_nonneg_right hX hS.le
    linarith
  have hu := hr.hx1
  have hcq : (d1 (I.S : ℝ) (I.H : ℝ)).1 -
      (place (I.S : ℝ) (I.H : ℝ) ((ratPoint (I.Tt (I.tau k))).1 + t,
        (ratPoint (I.Tt (I.tau k))).2)).1 < 0 := by
    simp only [d1, place]
    have : -(52 : ℝ) / I.S < ((ratPoint (I.Tt (I.tau k))).1 + t) / I.S := by
      rw [div_lt_div_iff_of_pos_right hS]; linarith
    have h52 : (52 : ℝ) / I.S < 1 := by
      rw [div_lt_one hS]; have := hsc.S_ge; linarith
    have : -(52 : ℝ) / I.S = -((52 : ℝ) / I.S) := by ring
    linarith
  rw [hg.recv_q hk, ratPoint_d1, det_eq_det2, det2_eq_lineXi (Oc (I.S : ℝ) (I.H : ℝ)) _ _ _
    hcq.ne]
  have b := band_d1 hsc hr hX'
  rw [abs_lt] at b
  have hz := xi_lXR (I := I) z
  have hZ := hg.Xis_eps hk (3 - 2 * t / 3)
  have he := hg.eps_eps
  refine mul_nonneg_of_nonpos_of_nonpos hcq.le ?_
  have h8 : (0 : ℝ) < 8 * I.S := by positivity
  have : 8 * (I.S : ℝ) * (xiOf (Oc (I.S : ℝ) (I.H : ℝ)) z -
      lineXi (Oc (I.S : ℝ) (I.H : ℝ)) (place (I.S : ℝ) (I.H : ℝ)
        ((ratPoint (I.Tt (I.tau k))).1 + t, (ratPoint (I.Tt (I.tau k))).2))
        (d1 (I.S : ℝ) (I.H : ℝ)) (z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1)) ≤ 0 := by
    have hb : 8 * (I.S : ℝ) *
        (Xis (I.S : ℝ) (ratPoint I.T0) (I.tau k) (3 - 2 * t / 3) - eps (I.S : ℝ) / 4) <
        8 * (I.S : ℝ) * lineXi (Oc (I.S : ℝ) (I.H : ℝ)) (place (I.S : ℝ) (I.H : ℝ)
        ((ratPoint (I.Tt (I.tau k))).1 + t, (ratPoint (I.Tt (I.tau k))).2))
          (d1 (I.S : ℝ) (I.H : ℝ)) (z.1 - (Oc (I.S : ℝ) (I.H : ℝ)).1) :=
      mul_lt_mul_of_pos_left (by linarith) h8
    rw [mul_sub, hz]
    rw [mul_sub, hZ, show 8 * (I.S : ℝ) * (eps (I.S : ℝ) / 4) = 1 / 4 by rw [← he]; ring] at hb
    simp only [rwR] at hξ
    linarith
  nlinarith

/-- **Below a line of slope one, west of a bound: below the axis.** -/
theorem Good.AR_neg_of_zeta {s : Point} {Z Xmax : ℝ} (hXm : |Xmax| ≤ 456 * N)
    (h1 : I.lYR s - I.lXR s ≤ Z) (h2 : I.lXR s ≤ Xmax)
    (h3 : Z + Xmax ≤ (I.lwR k + I.rwR k) / 2 - 17) : I.AR k s < 0 := by
  obtain ⟨E, hE, hEb⟩ := hg.AR_eq hk s
  obtain ⟨hD1, hD2⟩ := hg.DDR_bounds hk
  have hh := hg.hhR_abs hk
  obtain ⟨hN, hS, hS1, -, hSp, -⟩ := hg.S_big
  rw [abs_le] at hEb hh
  have hhX : |((I.hh k : ℚ) : ℝ) * Xmax| ≤ (3 * N + 50) * (456 * N) := by
    rw [abs_mul]; exact mul_le_mul (abs_le.2 hh) hXm (abs_nonneg _) (by linarith)
  rw [abs_le] at hhX
  have hDh : 0 ≤ ((I.DD k : ℚ) : ℝ) - ((I.hh k : ℚ) : ℝ) := by linarith
  have step : I.AR k s ≤ ((I.DD k : ℚ) : ℝ) * (Z + Xmax - ((I.lwR k + I.rwR k) / 2 - 16)) -
      ((I.hh k : ℚ) : ℝ) * Xmax + E := by
    rw [hE]
    have a1 : ((I.DD k : ℚ) : ℝ) * I.lYR s ≤ ((I.DD k : ℚ) : ℝ) * (Z + I.lXR s) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have a2 : (((I.DD k : ℚ) : ℝ) - ((I.hh k : ℚ) : ℝ)) * I.lXR s ≤
        (((I.DD k : ℚ) : ℝ) - ((I.hh k : ℚ) : ℝ)) * Xmax := mul_le_mul_of_nonneg_left h2 hDh
    nlinarith
  have a3 : ((I.DD k : ℚ) : ℝ) * (Z + Xmax - ((I.lwR k + I.rwR k) / 2 - 16)) ≤
      ((I.DD k : ℚ) : ℝ) * (-1) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have a4 : (3 * (N : ℝ) + 50) * (456 * N) + 4 * (17 * N + 100) * (14 * N + 50) < I.S := by
    rw [hS]; nlinarith
  linarith

/-- **Points of the umbra piece have `ζ ≤ ℓ`.** -/
theorem Good.umbra_zeta {z : Point} (hz : z ∈ hpSet (I.umbraFs k)) :
    I.lYR z - I.lXR z ≤ I.lwR k := by
  rw [mem_umbra_iff] at hz
  obtain ⟨-, -, h3, h4, -, -, -⟩ := hz
  obtain ⟨w1, w2⟩ := hg.wall_det hk z
  obtain ⟨z1x, z1y⟩ := hg.rl_z1 hk
  obtain ⟨-, -, -, -, -, hS, hw⟩ := hg.pairR hk
  obtain ⟨hN, -, hS1, -, hSp, h64⟩ := hg.S_big
  have h4' : 0 ≤ 64 * (I.S : ℝ) ^ 2 * ArtGallery.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) z :=
    mul_nonneg h64.le h4
  by_cases h : k + 1 < I.np
  · rw [w1 h] at h4'; linarith
  · rw [w2 h] at h4'
    rw [z1y] at h3
    have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
    rw [abs_le] at hw2
    obtain ⟨l1, -, -, -⟩ := hg.pairR hk
    by_cases hx : (I.rwR k - I.lwR k) / 2 - 3 ≤ I.lXR z
    · linarith
    · push Not at hx
      -- `A' (ζ − ℓ) ≤ (ℓ − 24)(X − X₀) ≤ 0` with `A' = 8S + X₀ > 0`
      have hA : 0 < 8 * (I.S : ℝ) + ((I.rwR k - I.lwR k) / 2 - 3) := by linarith
      have key : (8 * (I.S : ℝ) + ((I.rwR k - I.lwR k) / 2 - 3)) *
          ((I.lYR z - I.lXR z) - I.lwR k) ≤
          (I.lwR k - 24) * (I.lXR z - ((I.rwR k - I.lwR k) / 2 - 3)) := by nlinarith
      have : (I.lwR k - 24) * (I.lXR z - ((I.rwR k - I.lwR k) / 2 - 3)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      by_contra hcon
      push Not at hcon
      have := mul_pos hA (show 0 < (I.lYR z - I.lXR z) - I.lwR k by linarith)
      linarith

end Seg

end Input

end ArtGallery.Sec5.Corridor

end
