module

public import ArtGallery.Hardness.Sec5.Corridor.CoverRecvD

/-!
# Section 5: corridors — the copy guards see the umbra and the nook

Let `P` be any polygon whose region contains the corridor region, `g = p_k(t)` the base guard and
`q = q_k(t)` the receiver guard of pair `k` (`t ∈ [0, 3/2]`), and assume that `g` sees the
entrance and `q` sees the window in `P` (global hypotheses).

* `Good.base_sees_umbra`, `Good.recv_sees_umbra`: a point `z` of the umbra piece on the guard's
  side of its line through `c0` (resp. `c1`) is seen by the guard;
* `Good.base_sees_nook`, `Good.recv_sees_nook`: a point `z` of the nook piece strictly above the
  mouth, on the guard's side of its line through `z0` (resp. `z1`), is seen by the guard (the
  sight line passes through the mouth, docs/section5/08_proof_plan.md §9 (c)).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ}

section Views

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np) {P : Polygon}
  (hsub : I.poly.filled ⊆ P.filled)
include hg hk hsub

/-- **The base guard sees the umbra.** -/
theorem Good.base_sees_umbra {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2)
    (hent : ∀ w ∈ I.entrance, P.Sees ((I.umbraR k).p t) w) {z : Point}
    (hz : z ∈ hpSet (I.umbraFs k))
    (hc0 : 0 ≤ ArtGallery.det ((I.umbraR k).p t) (ratPoint (c0 I.S I.H)) z) :
    P.Sees ((I.umbraR k).p t) z := by
  obtain ⟨w, hw, hwg, hseg⟩ := hg.base_seg hk ht0 ht1 hz hc0
  exact sees_of_segment_split hwg (hent w hw) (hseg.trans hsub)

/-- **The receiver sees the umbra.** -/
theorem Good.recv_sees_umbra {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2)
    (hwin : ∀ w ∈ I.window, P.Sees ((I.umbraR k).q t) w) {z : Point}
    (hz : z ∈ hpSet (I.umbraFs k))
    (hc1 : ArtGallery.det ((I.umbraR k).q t) (ratPoint (c1 I.S I.H)) z ≤ 0) :
    P.Sees ((I.umbraR k).q t) z := by
  obtain ⟨w, hw, hwq, hseg⟩ := hg.recv_seg hk ht0 ht1 hz hc1
  exact sees_of_segment_split hwq (hwin w hw) (hseg.trans hsub)

omit hsub in
/-- The nook piece lies near the apex. -/
theorem Good.nook_box {z : Point} (hz : z ∈ hpSet (I.nookFs k)) :
    I.lXR (ratPoint (I.z0 k)) ≤ I.lXR z ∧ I.lXR z ≤ I.lXR (ratPoint (I.z1 k)) ∧
      I.lYR (ratPoint (I.z1 k)) ≤ I.lYR z ∧ I.lYR z ≤ (I.lwR k + I.rwR k) / 2 + 5 / 4 := by
  rw [mem_nook_iff] at hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  refine ⟨h1, h2, h3, ?_⟩
  obtain ⟨n1x, n1y⟩ := hg.rl_n1 hk
  obtain ⟨n0x, n0y⟩ := hg.rl_n0 hk
  obtain ⟨z1x, -⟩ := hg.rl_z1 hk
  obtain ⟨z0x, -⟩ := hg.rl_z0 hk
  obtain ⟨-, -, -, -, -, h64⟩ := hg.S_big
  rw [abs_le] at n1y n0y
  have h := mul_nonneg h64.le h4
  rw [det_lXR, n1x, n0x] at h
  rw [z1x] at h2; rw [z0x] at h1
  by_contra hc; push Not at hc
  nlinarith

omit hsub in
/-- Points of the mouth are in the nook piece and in the umbra piece. -/
theorem Good.mouth_mem {m : Point} (hy : I.lYR m = I.lYR (ratPoint (I.z1 k)))
    (hx0 : I.lXR (ratPoint (I.z0 k)) ≤ I.lXR m) (hx1 : I.lXR m ≤ I.lXR (ratPoint (I.z1 k))) :
    m ∈ hpSet (I.nookFs k) ∧ m ∈ hpSet (I.umbraFs k) := by
  obtain ⟨n1x, n1y⟩ := hg.rl_n1 hk
  obtain ⟨n0x, n0y⟩ := hg.rl_n0 hk
  obtain ⟨z1x, z1y⟩ := hg.rl_z1 hk
  obtain ⟨z0x, z0y⟩ := hg.rl_z0 hk
  obtain ⟨zx, -, -, -, -⟩ := hg.rl_zp hk
  obtain ⟨-, -, hS1, -, -, h64⟩ := hg.S_big
  obtain ⟨l1, l2, r1, r2, hN, hS, hw⟩ := hg.pairR hk
  obtain ⟨-, -, -, -, -⟩ := hg.rl_strip_ends hk
  have hnx : I.lXR (ratPoint (I.nxt k)) ≤ (I.rwR k - I.lwR k) / 2 - 53 := by
    have := hg.lX_nxt hk
    rw [lXR_ratPoint]; have h' := rat_cast_le_of this; push_cast at h'; simp only [lwR, rwR]
    exact h'
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at n1y n0y zx hw2
  constructor
  · rw [mem_nook_iff]
    refine ⟨hx0, hx1, hy.ge, ?_⟩
    refine nonneg_of_mul_nonneg_c h64 ?_
    rw [det_lXR, n1x, n0x, hy, z1y]
    rw [z1x] at hx1; rw [z0x] at hx0
    nlinarith
  · rw [mem_umbra_iff]
    refine ⟨(hg.AR_pos_of hk (by rw [abs_le]; constructor <;> linarith)
      (by rw [hy, z1y]; linarith)).le,
      hg.edge_quadrant hk hx1 hy.le, hy.le, hg.wall_quadrant hk hx0 (by rw [hy, z1y, z0y]),
      by linarith, by linarith, by rw [hy, z1y]; nlinarith⟩

/-- **The base guard sees the nook through the mouth.** -/
theorem Good.base_sees_nook {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2)
    (hent : ∀ w ∈ I.entrance, P.Sees ((I.umbraR k).p t) w) {z : Point}
    (hz : z ∈ hpSet (I.nookFs k)) (hzK : z ∈ I.poly.filled) (hzb : z ∉ I.poly.boundary)
    (hdet : ArtGallery.det ((I.umbraR k).p t) (ratPoint (I.z0 k)) z ≤ 0) :
    P.Sees ((I.umbraR k).p t) z := by
  obtain ⟨zx0, zx1, zy0, zy1⟩ := hg.nook_box hk hz
  obtain ⟨z1x, z1y⟩ := hg.rl_z1 hk
  obtain ⟨z0x, z0y⟩ := hg.rl_z0 hk
  obtain ⟨l1, l2, r1, r2, hN, hS, hw⟩ := hg.pairR hk
  obtain ⟨-, -, hS1, -, hSp, h64⟩ := hg.S_big
  obtain ⟨hg0, hg1, hg2, hgx⟩ := hg.base_x hk ht0 ht1
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw2
  set g := (I.umbraR k).p t with hgdef
  have hgy : I.lYR g = -(8 * I.S) * (I.H + 1) := by simp only [lYR, hg2]; ring
  have hH : (I.S : ℝ) + 1 ≤ I.H := hg.scaleR.hH1
  -- the mouth point
  obtain ⟨m, hmseg, hmy⟩ := exists_mem_segment_ev_eq (I.cA 0 1 0) (g := g) (z := z)
    (c := I.lYR (ratPoint (I.z1 k))) (by rw [ev_cA, hgy, z1y]; nlinarith)
    (by rw [ev_cA]; linarith)
  rw [ev_cA] at hmy
  have hmy' : I.lYR m = I.lYR (ratPoint (I.z1 k)) := by linarith
  obtain ⟨hmx, -, -⟩ := hg.base_mono hk ht0 ht1 (by rw [abs_le]; constructor <;> linarith)
    (by rw [abs_le]; constructor <;> linarith) hmseg
  have hmx0 : I.lXR (ratPoint (I.z0 k)) ≤ I.lXR m := by
    have hdm : ArtGallery.det g (ratPoint (I.z0 k)) m ≤ 0 := by
      obtain ⟨μ, hμ0, -, rfl⟩ := hmseg
      have : ArtGallery.det g (ratPoint (I.z0 k)) (g.1 + μ * (z.1 - g.1), g.2 + μ * (z.2 - g.2)) =
          μ * ArtGallery.det g (ratPoint (I.z0 k)) z := by simp only [ArtGallery.det]; ring
      rw [this]; exact mul_nonpos_of_nonneg_of_nonpos hμ0 hdet
    have e : 64 * (I.S : ℝ) ^ 2 * ArtGallery.det g (ratPoint (I.z0 k)) m =
        -(I.lXR m - I.lXR (ratPoint (I.z0 k))) * (I.lYR (ratPoint (I.z0 k)) - I.lYR g) := by
      rw [det_lXR]; rw [hmy', z1y, ← z0y]; ring
    have hpos : 0 < I.lYR (ratPoint (I.z0 k)) - I.lYR g := by rw [hgy, z0y]; nlinarith
    by_contra hc; push Not at hc
    have : 0 < 64 * (I.S : ℝ) ^ 2 * ArtGallery.det g (ratPoint (I.z0 k)) m := by
      rw [e]; nlinarith
    nlinarith
  obtain ⟨hmN, hmU⟩ := hg.mouth_mem hk hmy' hmx0 (hmx.trans zx1)
  -- `g` sees the mouth point
  have hc0 : 0 ≤ ArtGallery.det g (ratPoint (c0 I.S I.H)) m :=
    hg.base_c0_nonneg hk ht0 ht1 (by rw [abs_le]; constructor <;> linarith)
      (by rw [hmy', z1y]; linarith)
  have hgm := hg.base_sees_umbra hk hsub ht0 ht1 hent hmU hc0
  -- the rest of the sight line is in the nook
  have hnook := hg.nook_subset hk hz hzK hzb
  intro x hx
  rcases segment_subset_union hmseg hx with h | h
  · exact hgm h
  · exact hsub (hnook (Geometry.segment_subset_of_convex (convex_hpSet _) hmN hz h))

/-- **The receiver sees the nook through the mouth.** -/
theorem Good.recv_sees_nook {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 2)
    (hwin : ∀ w ∈ I.window, P.Sees ((I.umbraR k).q t) w) {z : Point}
    (hz : z ∈ hpSet (I.nookFs k)) (hzK : z ∈ I.poly.filled) (hzb : z ∉ I.poly.boundary)
    (hdet : 0 ≤ ArtGallery.det ((I.umbraR k).q t) (ratPoint (I.z1 k)) z) :
    P.Sees ((I.umbraR k).q t) z := by
  obtain ⟨zx0, zx1, zy0, zy1⟩ := hg.nook_box hk hz
  obtain ⟨z1x, z1y⟩ := hg.rl_z1 hk
  obtain ⟨z0x, z0y⟩ := hg.rl_z0 hk
  obtain ⟨l1, l2, r1, r2, hN, hS, hw⟩ := hg.pairR hk
  obtain ⟨-, -, hS1, -, hSp, h64⟩ := hg.S_big
  obtain ⟨qx, qy⟩ := hg.rl_recv hk t
  obtain ⟨u1, u2, w1, w2, -⟩ := hg.recv_atoms hk
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw2
  set q := (I.umbraR k).q t with hqdef
  -- the mouth point
  obtain ⟨m, hmseg, hmy⟩ := exists_mem_segment_ev_eq (I.cA 0 1 0) (g := q) (z := z)
    (c := I.lYR (ratPoint (I.z1 k))) (by rw [ev_cA, qy, z1y]; nlinarith)
    (by rw [ev_cA]; linarith)
  rw [ev_cA] at hmy
  have hmy' : I.lYR m = I.lYR (ratPoint (I.z1 k)) := by linarith
  have hmx : I.lXR z ≤ I.lXR m := by
    obtain ⟨μ, hμ0, hμ1, rfl⟩ := hmseg
    have e : I.lXR (q.1 + μ * (z.1 - q.1), q.2 + μ * (z.2 - q.2)) - I.lXR z =
        (1 - μ) * (I.lXR q - I.lXR z) := by simp only [lXR]; ring
    have : 0 ≤ (1 - μ) * (I.lXR q - I.lXR z) :=
      mul_nonneg (by linarith) (by rw [qx]; nlinarith)
    linarith
  have hmx1 : I.lXR m ≤ I.lXR (ratPoint (I.z1 k)) := by
    have hdm : 0 ≤ ArtGallery.det q (ratPoint (I.z1 k)) m := by
      obtain ⟨μ, hμ0, -, rfl⟩ := hmseg
      have : ArtGallery.det q (ratPoint (I.z1 k)) (q.1 + μ * (z.1 - q.1), q.2 + μ * (z.2 - q.2)) =
          μ * ArtGallery.det q (ratPoint (I.z1 k)) z := by simp only [ArtGallery.det]; ring
      rw [this]; exact mul_nonneg hμ0 hdet
    have e : 64 * (I.S : ℝ) ^ 2 * ArtGallery.det q (ratPoint (I.z1 k)) m =
        -(I.lXR m - I.lXR (ratPoint (I.z1 k))) * (I.lYR (ratPoint (I.z1 k)) - I.lYR q) := by
      rw [det_lXR, hmy']; ring
    have hpos : 0 < I.lYR (ratPoint (I.z1 k)) - I.lYR q := by rw [qy, z1y]; nlinarith
    by_contra hc; push Not at hc
    have : 64 * (I.S : ℝ) ^ 2 * ArtGallery.det q (ratPoint (I.z1 k)) m < 0 := by
      rw [e]; nlinarith
    nlinarith
  obtain ⟨hmN, hmU⟩ := hg.mouth_mem hk hmy' (zx0.trans hmx) hmx1
  have hc1 : ArtGallery.det q (ratPoint (c1 I.S I.H)) m ≤ 0 :=
    hg.recv_c1_nonpos hk ht0 ht1 (by rw [abs_le]; constructor <;> linarith)
      (by rw [hmy', z1y]; rw [z0x] at zx0; linarith)
  have hqm := hg.recv_sees_umbra hk hsub ht0 ht1 hwin hmU hc1
  have hnook := hg.nook_subset hk hz hzK hzb
  intro x hx
  rcases segment_subset_union hmseg hx with h | h
  · exact hqm h
  · exact hsub (hnook (Geometry.segment_subset_of_convex (convex_hpSet _) hmN hz h))

end Views

end Input

end ArtGallery.Sec5.Corridor

end
