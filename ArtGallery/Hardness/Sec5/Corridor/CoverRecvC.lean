module

public import ArtGallery.Hardness.Sec5.Corridor.CoverRecv

/-!
# Section 5: corridors — the receivers see the umbra through the window (main lemma)

`Good.recv_seg`: for a point `z` of the umbra piece of pair `k` with `det(q, c1, z) ≤ 0`, the
sight line from the receiver `q` crosses the window at `w` and `[w, z]` lies in the corridor
region (see `CoverRecv.lean`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ}

section Recv

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

/-- Points of the window are below every axis. -/
theorem Good.AR_window_neg {w : Point} (hw : w ∈ I.window) : I.AR k w < 0 := by
  have hρ := hg.rhoR_pos
  obtain ⟨μ, h0, h1, rfl⟩ := hw
  obtain ⟨E, hE, hEb⟩ := hg.AR_eq hk (((ratPoint (c1 I.S I.H)).1 + μ *
      ((ratPoint (d1 I.S I.H)).1 - (ratPoint (c1 I.S I.H)).1),
    (ratPoint (c1 I.S I.H)).2 + μ * ((ratPoint (d1 I.S I.H)).2 - (ratPoint (c1 I.S I.H)).2)))
  obtain ⟨hD1, hD2⟩ := hg.DDR_bounds hk
  have hh := hg.hhR_abs hk
  obtain ⟨hN, hS, hS1, -, hSp, -⟩ := hg.S_big
  obtain ⟨l1, l2, r1, r2, -, -, hw⟩ := hg.pairR hk
  rw [abs_le] at hEb hh
  rw [hE]
  rw [ratPoint_c1', ratPoint_d1']
  simp only [lXR, lYR]
  have hx : 8 * (I.S : ℝ) * ((I.S : ℝ) + 2 + μ * ((I.S : ℝ) + 2 - ((I.S : ℝ) + 2)) - ((I.S : ℝ) + 1))
      = 8 * I.S := by ring
  have hy : 8 * (I.S : ℝ) * ((I.H : ℝ) + μ * ((I.H : ℝ) + I.rhoR - (I.H : ℝ)) - ((I.H : ℝ) + 1)) ≤
      -(8 * I.S) + 12 := by
    rw [rhoR_eq]
    have : 8 * (I.S : ℝ) * (μ * (3 / (2 * I.S))) = 12 * μ := by field_simp; ring
    nlinarith
  rw [hx]
  have hf : 8 * (I.S : ℝ) * ((I.H : ℝ) + μ * ((I.H : ℝ) + I.rhoR - (I.H : ℝ)) - ((I.H : ℝ) + 1)) -
      ((I.lwR k + I.rwR k) / 2 - 16) ≤ -(7 * (I.S : ℝ)) := by nlinarith
  have h7 : ((I.DD k : ℚ) : ℝ) * (8 * (I.S : ℝ) * ((I.H : ℝ) + μ * ((I.H : ℝ) + I.rhoR -
      (I.H : ℝ)) - ((I.H : ℝ) + 1)) - ((I.lwR k + I.rwR k) / 2 - 16)) ≤ (I.S : ℝ) * (-(7 * I.S)) :=
    (mul_le_mul_of_nonpos_right hD1 (by linarith)).trans (mul_le_mul_of_nonneg_left hf hSp.le)
  have h8 : |((I.hh k : ℚ) : ℝ) * (8 * I.S)| ≤ (3 * N + 50) * (8 * I.S) := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 8 * I.S)]
    exact mul_le_mul_of_nonneg_right (abs_le.2 hh) (by linarith)
  rw [abs_le] at h8
  have h9 : (3 * (N : ℝ) + 50) * (8 * I.S) + 4 * (17 * N + 100) * (14 * N + 50) <
      (I.S : ℝ) * (7 * I.S) := by nlinarith
  linarith

/-- The sight line of the receiver towards a point of the umbra piece in its band crosses the
window. -/
theorem Good.recv_window {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2) {z : Point}
    (hz : z ∈ hpSet (I.umbraFs k))
    (hc1 : ArtGallery.det ((I.umbraR k).q t) (ratPoint (c1 I.S I.H)) z ≤ 0) :
    ∃ w ∈ I.window, w ∈ ArtGallery.segment ((I.umbraR k).q t) z := by
  obtain ⟨zX1, zX2, zY1, zY2⟩ := hg.umbra_box hk hz
  have hξ := hg.umbra_xi hk hz
  obtain ⟨l1, l2, r1, r2, hN, hS, hww⟩ := hg.pairR hk
  obtain ⟨-, -, hS1, -, hSp, -⟩ := hg.S_big
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw2
  have hzw : |I.lXR z| ≤ 456 * N := by rw [abs_le]; constructor <;> linarith
  have hd1 := hg.recv_d1_nonneg hk ht0 ht1 hzw hξ
  obtain ⟨qx, -⟩ := hg.rl_recv hk t
  obtain ⟨u1, u2, -, -, -⟩ := hg.recv_atoms hk
  set q := (I.umbraR k).q t with hqdef
  have hS8 : (0 : ℝ) < 8 * I.S := by linarith
  have hqx : (I.S : ℝ) + 2 + 1 / 2 ≤ q.1 := by
    have e : q.1 = I.S + 1 + I.lXR q / (8 * I.S) := by simp only [lXR]; field_simp; ring
    rw [e, qx]
    have : (3 / 2 : ℝ) ≤ (16 * I.S + 8 * (((I.tu k : ℚ) : ℝ) + t)) / (8 * I.S) := by
      rw [le_div_iff₀ hS8]; nlinarith
    linarith
  have hzx : z.1 ≤ (I.S : ℝ) + 2 := by
    have e : z.1 = I.S + 1 + I.lXR z / (8 * I.S) := by simp only [lXR]; field_simp; ring
    rw [e]
    have : I.lXR z / (8 * I.S) ≤ 1 := by rw [div_le_iff₀ hS8]; nlinarith
    linarith
  obtain ⟨w, hwseg, hwx⟩ := exists_mem_segment_ev_eq ⟨-1, 0, 0⟩ (g := q) (z := z)
    (c := -((I.S : ℝ) + 2)) (by simp only [Aff.ev]; linarith) (by simp only [Aff.ev]; linarith)
  simp only [Aff.ev, zero_mul, add_zero] at hwx
  have hwx' : w.1 = I.S + 2 := by linarith
  refine ⟨w, ?_, hwseg⟩
  obtain ⟨μ, hμ0, hμ1, hwdef⟩ := hwseg
  have hdet : ∀ a : Point, ArtGallery.det q a w = μ * ArtGallery.det q a z := by
    intro a; rw [hwdef]; simp only [ArtGallery.det]; ring
  have hρ := hg.rhoR_pos
  have hgx' : (I.S : ℝ) + 2 - q.1 < 0 := by linarith
  have e1 : ArtGallery.det q (ratPoint (c1 I.S I.H)) w = ((I.S : ℝ) + 2 - q.1) * (w.2 - I.H) := by
    rw [ratPoint_c1']; simp only [ArtGallery.det, hwx']; ring
  have e2 : ArtGallery.det q (ratPoint (d1 I.S I.H)) w =
      ((I.S : ℝ) + 2 - q.1) * (w.2 - (I.H + I.rhoR)) := by
    rw [ratPoint_d1']; simp only [ArtGallery.det, hwx']; ring
  have hy1 : (I.H : ℝ) ≤ w.2 := by
    have h := hdet (ratPoint (c1 I.S I.H))
    rw [e1] at h
    have : ((I.S : ℝ) + 2 - q.1) * (w.2 - I.H) ≤ 0 := by
      rw [h]; exact mul_nonpos_of_nonneg_of_nonpos hμ0 hc1
    by_contra hc; push Not at hc
    have := mul_pos_of_neg_of_neg hgx' (show w.2 - I.H < 0 by linarith)
    linarith
  have hy2 : w.2 ≤ (I.H : ℝ) + I.rhoR := by
    have h := hdet (ratPoint (d1 I.S I.H))
    rw [e2] at h
    have : 0 ≤ ((I.S : ℝ) + 2 - q.1) * (w.2 - (I.H + I.rhoR)) := by
      rw [h]; exact mul_nonneg hμ0 hd1
    by_contra hc; push Not at hc
    have := mul_neg_of_neg_of_pos hgx' (show 0 < w.2 - (I.H + I.rhoR) by linarith)
    linarith
  refine ⟨(w.2 - I.H) / I.rhoR, div_nonneg (by linarith) hρ.le,
    (div_le_one hρ).2 (by linarith), ?_⟩
  rw [ratPoint_c1', ratPoint_d1']
  ext
  · simp only; rw [hwx']; ring
  · simp only; field_simp; ring

end Recv

section East

variable (hg : I.Good N)
include hg

/-- The constant `e = 1/(500 N)`. -/
theorem Good.e_facts : 0 < 1 / (500 * (N : ℝ)) ∧ 1 / (500 * (N : ℝ)) * N = 1 / 500 ∧
    1 / (500 * (N : ℝ)) ≤ 1 / 1000 := by
  obtain ⟨hN, -⟩ := hg.S_big
  have hNp : (0 : ℝ) < N := by linarith
  refine ⟨by positivity, by field_simp, ?_⟩
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith

/-- **East of the valley, adjacent strip.**  A point of the strip of pair `j`, east of the valley
`v_{j+1}` and left of `q_{j+1} → v_{j+1}`, lies in the strip piece of `j`. -/
theorem Good.recv_east_adj {j : ℕ} (hj : j + 1 < I.np) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2)
    {s : Point} (hq : 0 ≤ ArtGallery.det ((I.umbraR (j + 1)).q t) (ratPoint (I.valley (j + 1))) s)
    (hj1 : I.lXR (ratPoint (I.nxt j)) ≤ I.lXR s) (hj2 : I.lXR s ≤ I.lXR (ratPoint (I.sgPt j)))
    (hsH : -(8 * (I.S : ℝ)) ≤ I.lYR s) : s ∈ I.poly.filled := by
  have hj' : j < I.np := by omega
  obtain ⟨vx, vy⟩ := hg.rl_valley hj (by omega)
  rw [show j + 1 - 1 = j by omega] at vx vy
  obtain ⟨n1, -⟩ := hg.rl_nxt hj'
  obtain ⟨nx, ny⟩ := n1 hj
  have hr := hg.rw_succ hj
  have hnv : I.lXR (ratPoint (I.nxt j)) = I.lXR (ratPoint (I.valley (j + 1))) := by
    rw [nx, vx, hr]; ring
  have hbv := hg.below_valley hj ht0 ht1 (by omega) hq (by rw [← hnv]; exact hj1)
  obtain ⟨he0, -, he2⟩ := hg.e_facts
  obtain ⟨hN, -, hS1, -, hSp, h64⟩ := hg.S_big
  obtain ⟨l1, l2, r1, r2, -, -, hw⟩ := hg.pairR hj'
  have hw2 : |(I.rwR j - I.lwR j) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw2
  set e := 1 / (500 * (N : ℝ))
  have hd0 : 0 ≤ I.lXR s - I.lXR (ratPoint (I.valley (j + 1))) := by linarith
  refine hg.strip_subset hj' ?_
  rw [mem_strip_iff]
  refine ⟨hj2, hj1, hsH, ?_, ?_⟩
  · refine (hg.AR_neg_of_line hj' (X0 := I.lXR (ratPoint (I.valley (j + 1))))
      (Y0 := I.lYR (ratPoint (I.valley (j + 1)))) (m := 1 - e)
      (Xmin := I.lXR (ratPoint (I.valley (j + 1)))) (by linarith) (by linarith) ?_ (by linarith)
      (by linarith) ?_).le
    · rw [vx, hr, abs_le]; constructor <;> linarith
    · rw [vy, hr]; linarith
  · obtain ⟨w1, -⟩ := hg.wall_det hj' s
    refine nonneg_of_mul_nonneg_c h64 ?_
    rw [w1 hj]
    have hζv : I.lYR (ratPoint (I.valley (j + 1))) - I.lXR (ratPoint (I.valley (j + 1))) =
        I.lwR j := by rw [vx, vy]; ring
    have : 0 ≤ (1 - e) * (I.lXR s - I.lXR (ratPoint (I.valley (j + 1)))) :=
      mul_nonneg (by linarith) hd0
    nlinarith

/-- **East of the valley, far strip** (three pairs, receiver of pair `2`, strip of pair `0`). -/
theorem Good.recv_east_far (h3 : 2 < I.np) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2)
    {s : Point} (hq : 0 ≤ ArtGallery.det ((I.umbraR 2).q t) (ratPoint (I.valley 2)) s)
    (hj1 : I.lXR (ratPoint (I.nxt 0)) ≤ I.lXR s) (hj2 : I.lXR s ≤ I.lXR (ratPoint (I.sgPt 0)))
    (hsH : -(8 * (I.S : ℝ)) ≤ I.lYR s) : s ∈ I.poly.filled := by
  obtain ⟨vx, vy⟩ := hg.rl_valley (k := 2) h3 (by omega)
  obtain ⟨wx, wy⟩ := hg.rl_valley (k := 1) (by omega) (by omega)
  simp only [show (2 : ℕ) - 1 = 1 from rfl, show (1 : ℕ) - 1 = 0 from rfl] at vx vy wx wy
  obtain ⟨n1, -⟩ := hg.rl_nxt (k := 0) (by omega)
  obtain ⟨nx, ny⟩ := n1 (by omega)
  have hr1 := hg.rw_succ (j := 0) (by omega)
  have hr2 := hg.rw_succ (j := 1) (by omega)
  have hl1 := hg.lw_succ (j := 0) (by omega)
  simp only [show (0 : ℕ) + 1 = 1 from rfl, show (1 : ℕ) + 1 = 2 from rfl] at hr1 hr2 hl1
  have hX : I.lXR (ratPoint (I.valley 2)) ≤ I.lXR s := by
    rw [nx] at hj1; rw [vx]; linarith
  have hbv := hg.below_valley h3 ht0 ht1 (by omega) hq hX
  obtain ⟨he0, he1, he2⟩ := hg.e_facts
  obtain ⟨hN, -, hS1, -, hSp, h64⟩ := hg.S_big
  obtain ⟨l1, l2, r1, r2, -, -, hw⟩ := hg.pairR (k := 0) (by omega)
  obtain ⟨l1', l2', -, -, -, -, -⟩ := hg.pairR (k := 1) (by omega)
  have hw2 : |(I.rwR 0 - I.lwR 0) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw2
  set e := 1 / (500 * (N : ℝ))
  -- the gap between the valleys
  have hgap : (108 + I.lwR 1 - I.lwR 0) / 2 ≤ I.lXR s - I.lXR (ratPoint (I.valley 2)) := by
    rw [nx] at hj1; rw [vx, hr2]; linarith
  have hgapE : e * ((108 + I.lwR 1 - I.lwR 0) / 2) ≤ 1 := by
    have : (108 + I.lwR 1 - I.lwR 0) / 2 ≤ 54 + 68 * N + 5 := by linarith
    nlinarith
  have hm : (1 - e) * ((108 + I.lwR 1 - I.lwR 0) / 2) ≤
      (1 - e) * (I.lXR s - I.lXR (ratPoint (I.valley 2))) :=
    mul_le_mul_of_nonneg_left hgap (by linarith)
  refine hg.strip_subset (k := 0) (by omega) ?_
  rw [mem_strip_iff]
  refine ⟨hj2, hj1, hsH, ?_, ?_⟩
  · refine (hg.AR_neg_of_line (k := 0) (by omega) (X0 := I.lXR (ratPoint (I.valley 2)))
      (Y0 := I.lYR (ratPoint (I.valley 2))) (m := 1 - e)
      (Xmin := I.lXR (ratPoint (I.valley 2)) + (108 + I.lwR 1 - I.lwR 0) / 2)
      (by linarith) (by linarith) ?_ ?_ (by linarith) ?_).le
    · rw [vx, hr2, hr1, abs_le]; constructor <;> linarith
    · linarith
    · rw [vy, hr2, hr1]
      have : (1 - e) * (I.lXR (ratPoint (I.valley 2)) + (108 + I.lwR 1 - I.lwR 0) / 2 -
          I.lXR (ratPoint (I.valley 2))) = (108 + I.lwR 1 - I.lwR 0) / 2 -
          e * ((108 + I.lwR 1 - I.lwR 0) / 2) := by ring
      rw [this]; linarith
  · obtain ⟨w1, -⟩ := hg.wall_det (k := 0) (by omega) s
    refine nonneg_of_mul_nonneg_c h64 ?_
    rw [w1 (by omega)]
    have hζv : I.lYR (ratPoint (I.valley 2)) - I.lXR (ratPoint (I.valley 2)) = I.lwR 1 := by
      rw [vx, vy]; ring
    have : I.lYR s - I.lXR s ≤ I.lwR 0 := by
      have e2 : (1 - e) * ((108 + I.lwR 1 - I.lwR 0) / 2) = (108 + I.lwR 1 - I.lwR 0) / 2 -
          e * ((108 + I.lwR 1 - I.lwR 0) / 2) := by ring
      linarith
    nlinarith

end East


end Input

end ArtGallery.Sec5.Corridor

end
