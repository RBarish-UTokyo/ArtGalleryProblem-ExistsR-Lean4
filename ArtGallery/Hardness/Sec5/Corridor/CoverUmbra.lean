module

public import ArtGallery.Hardness.Sec5.Corridor.CoverStrip

/-!
# Section 5: corridors — the umbra region and the nook (pieces)

For pair `k`:

* the **umbra piece** `hpSet (I.umbraFs k)`: above the umbra axis `A_k`, left of the upper-wall
  edge `z'_k → z1`, below the mouth level `y = y(z1)`, left of the wall `z0 → nxt_k` (the region
  of the corridor above `A_k` and below the nook mouth); `Good.umbra_subset`: it lies in the
  corridor region (anchored at an umbra critical point, `Good.umbra_crit_mem`);
* the **nook piece** `hpSet (I.nookFs k)`: the quadrilateral `z1, n1, n0, z0` (between the
  vertical lines through `z0`, `z1`, above the mouth, below the nook top edge);
  `Good.nook_subset`: it lies in the corridor region as soon as one of its points is an interior
  point of the corridor.

`Good.edge_det`: the edge `z'_k → z1` in local coordinates.
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ}

/-- The constraints of the umbra piece of pair `k`. -/
noncomputable def umbraFs (I : Input) (k : ℕ) : List Aff :=
  [I.cA (-((I.hh k : ℚ) : ℝ)) ((I.DD k : ℚ) : ℝ) (-(8 * I.S * ((I.gg k : ℚ) : ℝ))),
    Aff.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)),
    I.cA 0 (-1) (I.lYR (ratPoint (I.z1 k))),
    Aff.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)),
    I.cA (-1) 0 (I.lXR (ratPoint (I.zp k))), I.cA 1 0 (-I.lXR (ratPoint (I.nxt k))),
    I.cA 0 1 (8 * I.S)]

theorem mem_umbra_iff {k : ℕ} {z : Point} :
    z ∈ hpSet (I.umbraFs k) ↔ 0 ≤ I.AR k z ∧
      0 ≤ ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)) z ∧
      I.lYR z ≤ I.lYR (ratPoint (I.z1 k)) ∧
      0 ≤ ArtGallery.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) z ∧
      I.lXR z ≤ I.lXR (ratPoint (I.zp k)) ∧ I.lXR (ratPoint (I.nxt k)) ≤ I.lXR z ∧
      -(8 * (I.S : ℝ)) ≤ I.lYR z := by
  simp only [hpSet, umbraFs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, ev_cA, Aff.ev_det, Set.mem_ofPred_eq, AR]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨by linarith, h2, by linarith, h4, by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨by linarith, h2, by linarith, h4, by linarith, by linarith, by linarith⟩

theorem mem_umbraOpen_iff {k : ℕ} {z : Point} :
    z ∈ hpOpen (I.umbraFs k) ↔ 0 < I.AR k z ∧
      0 < ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)) z ∧
      I.lYR z < I.lYR (ratPoint (I.z1 k)) ∧
      0 < ArtGallery.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) z ∧
      I.lXR z < I.lXR (ratPoint (I.zp k)) ∧ I.lXR (ratPoint (I.nxt k)) < I.lXR z ∧
      -(8 * (I.S : ℝ)) < I.lYR z := by
  simp only [hpOpen, umbraFs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, ev_cA, Aff.ev_det, Set.mem_ofPred_eq, AR]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨by linarith, h2, by linarith, h4, by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨by linarith, h2, by linarith, h4, by linarith, by linarith, by linarith⟩

/-- The constraints of the nook piece of pair `k`. -/
noncomputable def nookFs (I : Input) (k : ℕ) : List Aff :=
  [I.cA 1 0 (-I.lXR (ratPoint (I.z0 k))), I.cA (-1) 0 (I.lXR (ratPoint (I.z1 k))),
    I.cA 0 1 (-I.lYR (ratPoint (I.z1 k))), Aff.det (ratPoint (I.n1 k)) (ratPoint (I.n0 k))]

theorem mem_nook_iff {k : ℕ} {z : Point} :
    z ∈ hpSet (I.nookFs k) ↔ I.lXR (ratPoint (I.z0 k)) ≤ I.lXR z ∧
      I.lXR z ≤ I.lXR (ratPoint (I.z1 k)) ∧ I.lYR (ratPoint (I.z1 k)) ≤ I.lYR z ∧
      0 ≤ ArtGallery.det (ratPoint (I.n1 k)) (ratPoint (I.n0 k)) z := by
  simp only [hpSet, nookFs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, ev_cA, Aff.ev_det, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨by linarith, by linarith, by linarith, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨by linarith, by linarith, by linarith, h4⟩

section Pieces

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

/-- **The edge `z'_k → z1` in local coordinates**: with `ξ = lX + lY`,
`64 S² det(z'_k, z1, P) = (X₁ − X') (ξ_P − ξ') − (X_P − X') (r − ξ')`. -/
theorem Good.edge_det (P : Point) :
    64 * (I.S : ℝ) ^ 2 * ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)) P =
      (I.lXR (ratPoint (I.z1 k)) - I.lXR (ratPoint (I.zp k))) *
          ((I.lXR P + I.lYR P) - (I.lXR (ratPoint (I.zp k)) + I.lYR (ratPoint (I.zp k)))) -
        (I.lXR P - I.lXR (ratPoint (I.zp k))) *
          (I.rwR k - (I.lXR (ratPoint (I.zp k)) + I.lYR (ratPoint (I.zp k)))) := by
  rw [det_lXR]
  have b1 := hg.rl_z1 hk
  have e : I.lYR (ratPoint (I.z1 k)) = I.rwR k - I.lXR (ratPoint (I.z1 k)) := by
    rw [b1.1, b1.2]; ring
  rw [e]; ring

/-- Points with `ξ ≤ r − 1` near the apex are strictly left of the edge `z'_k → z1`. -/
theorem Good.edge_pos {P : Point} (hξ : I.lXR P + I.lYR P ≤ I.rwR k - 1)
    (hX : |I.lXR P - (I.rwR k - I.lwR k) / 2| ≤ 20) :
    0 < ArtGallery.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)) P := by
  have e := hg.edge_det hk P
  obtain ⟨z1x, z1y⟩ := hg.rl_z1 hk
  obtain ⟨zx, -, zξ1, zξ2, -⟩ := hg.rl_zp hk
  obtain ⟨-, -, -, -, hN, hS, -⟩ := hg.pairR hk
  have h64 : (0 : ℝ) < 64 * (I.S : ℝ) ^ 2 := by rw [hS]; positivity
  rw [abs_le] at zx hX
  refine pos_of_mul_pos_right ?_ h64.le
  rw [e, z1x]
  nlinarith

/-- The anchor of the umbra piece: an umbra critical point. -/
theorem Good.umbra_anchor : ∃ c : Point, c ∈ hpOpen (I.umbraFs k) ∧
    c ∈ I.poly.filled \ I.poly.boundary := by
  -- the anchor: an umbra critical point
  set c := (I.umbraR k).X 1 (1 / 2) with hcdef
  have hcK := hg.umbra_crit_mem hk (v₀ := 1) (v₁ := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [← hcdef] at hcK
  obtain ⟨cz1, cz2, cx1, cx2, cX, cY1, cY2⟩ :=
    hg.umbra_crit_eps hk (v₀ := 1) (v₁ := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  rw [← hcdef] at cz1 cz2 cx1 cx2 cX cY1 cY2
  change I.lYR c - I.lXR c ≤ I.lwR k - 99 / 10 at cz2
  change I.rwR k - 89 / 4 ≤ I.lYR c + I.lXR c at cx1
  change I.lYR c + I.lXR c ≤ I.rwR k - 39 / 4 at cx2
  change |I.lXR c - (I.rwR k - I.lwR k) / 2| ≤ 31 / 5 at cX
  change (I.lwR k + I.rwR k) / 2 - 111 / 5 ≤ I.lYR c at cY1
  change I.lYR c ≤ (I.lwR k + I.rwR k) / 2 - 49 / 5 at cY2
  obtain ⟨l1, l2, r1, r2, hN, hS, hw⟩ := hg.pairR hk
  obtain ⟨e1, e2, e3, e4, e5⟩ := hg.rl_strip_ends hk
  obtain ⟨zx, zy, zξ1, zξ2, zA⟩ := hg.rl_zp hk
  obtain ⟨z1x, z1y⟩ := hg.rl_z1 hk
  obtain ⟨z0x, z0y⟩ := hg.rl_z0 hk
  obtain ⟨n1x, n1y⟩ := hg.rl_n1 hk
  obtain ⟨n0x, n0y⟩ := hg.rl_n0 hk
  have hnx : I.lXR (ratPoint (I.nxt k)) ≤ (I.rwR k - I.lwR k) / 2 - 53 := by
    have := hg.lX_nxt hk
    rw [lXR_ratPoint]; have h' := rat_cast_le_of this; push_cast at h'; simp only [lwR, rwR]
    exact h'
  have hzpp : I.lXR (ratPoint (I.zp k)) < I.lXR (ratPoint (I.sgPt k)) := by
    rw [lXR_ratPoint, lXR_ratPoint]
    exact_mod_cast (fst_lt_iff hg).1 (hg.zp_lt_sgPt hk)
  rw [abs_le] at zx zy cX n1y n0y
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw2
  have hc : c ∈ hpOpen (I.umbraFs k) := by
    rw [mem_umbraOpen_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- strictly above the axis
      have hC := umbraR_hyp hg.toValid k
      have hA := umbraR_adm hg.toValid hk
      have hG := CopyPair.G_pos hC hA (t₀ := 1) (t₁ := 1 / 2) (by norm_num) (by norm_num)
      have hwp := CopyPair.w_X_pos hC hA (t₀ := 1) (t₁ := 1 / 2) (by norm_num) (by norm_num)
      have hL := (I.umbraR k).L_X hC.hk hG.ne'
      rw [← hcdef] at hL hwp
      rw [← hg.umbraR_L_AR, hL]
      have hs0 := hC.hs0; have hs1 := hC.hs1
      have hSp : (0 : ℝ) < I.S := by rw [hS]; positivity
      have : 0 < (I.umbraR k).s0 * (I.umbraR k).s1 * (I.umbraR k).w c * (1 - 1 / 2) := by
        have := mul_pos (mul_pos hs0 hs1) hwp; nlinarith
      positivity
    · exact hg.edge_pos hk (by linarith) (by rw [abs_le]; constructor <;> linarith)
    · rw [z1y]; linarith
    · exact hg.wall_of_window hk (by rw [abs_le]; constructor <;> linarith)
        (by rw [abs_le]; constructor <;> linarith) (by linarith)
    · linarith
    · linarith
    · have : (1000 : ℝ) ≤ I.S := by obtain ⟨-, -, h1, -⟩ := hg.S_big; linarith
      linarith
  exact ⟨c, hc, hcK⟩

/-- The boundary check of the umbra piece. -/
theorem Good.umbra_bd : ∀ w ∈ I.poly.boundary, ∃ f ∈ I.umbraFs k, f.ev w ≤ 0 := by
  obtain ⟨l1, l2, r1, r2, hN, hS, hw⟩ := hg.pairR hk
  obtain ⟨e1, e2, e3, e4, e5⟩ := hg.rl_strip_ends hk
  obtain ⟨zx, zy, zξ1, zξ2, zA⟩ := hg.rl_zp hk
  obtain ⟨z1x, z1y⟩ := hg.rl_z1 hk
  obtain ⟨z0x, z0y⟩ := hg.rl_z0 hk
  obtain ⟨n1x, n1y⟩ := hg.rl_n1 hk
  obtain ⟨n0x, n0y⟩ := hg.rl_n0 hk
  have hnx : I.lXR (ratPoint (I.nxt k)) ≤ (I.rwR k - I.lwR k) / 2 - 53 := by
    have := hg.lX_nxt hk
    rw [lXR_ratPoint]; have h' := rat_cast_le_of this; push_cast at h'; simp only [lwR, rwR]
    exact h'
  have hzpp : I.lXR (ratPoint (I.zp k)) < I.lXR (ratPoint (I.sgPt k)) := by
    rw [lXR_ratPoint, lXR_ratPoint]
    exact_mod_cast (fst_lt_iff hg).1 (hg.zp_lt_sgPt hk)
  rw [abs_le] at zx zy n1y n0y
  have m1 : I.cA (-((I.hh k : ℚ) : ℝ)) ((I.DD k : ℚ) : ℝ) (-(8 * I.S * ((I.gg k : ℚ) : ℝ))) ∈
      I.umbraFs k := by simp [umbraFs]
  have m2 : Aff.det (ratPoint (I.zp k)) (ratPoint (I.z1 k)) ∈ I.umbraFs k := by simp [umbraFs]
  have m3 : I.cA 0 (-1) (I.lYR (ratPoint (I.z1 k))) ∈ I.umbraFs k := by simp [umbraFs]
  have m4 : Aff.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) ∈ I.umbraFs k := by simp [umbraFs]
  have m5 : I.cA (-1) 0 (I.lXR (ratPoint (I.zp k))) ∈ I.umbraFs k := by simp [umbraFs]
  have m6 : I.cA 1 0 (-I.lXR (ratPoint (I.nxt k))) ∈ I.umbraFs k := by simp [umbraFs]
  have m7 : I.cA 0 1 (8 * I.S) ∈ I.umbraFs k := by simp [umbraFs]
  have hSN : 456 * (N : ℝ) + 1000 ≤ 8 * I.S := by
    obtain ⟨-, -, h1, -⟩ := hg.S_big; linarith
  refine hg.bd_check hk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine hg.floor_check m7 ?_
    intro w hw; rw [ev_cA]; have := (lYR_le_floor_iff hg).2 hw; linarith
  · refine ⟨_, m5, ?_, ?_⟩ <;> simp only [ev_cA, lXR_c1', lXR_d1'] <;> linarith
  · refine ⟨_, m6, ?_, ?_⟩ <;> simp only [ev_cA, lXR_c0', lXR_d0'] <;> linarith
  · refine ⟨_, m5, fun v hv => ?_⟩
    rw [ev_cA]; have := (lXR_le_iff' hg).2 (show (ratPoint (I.sgPt k)).1 ≤ (ratPoint v).1 by
      simp only [ratPoint]; exact_mod_cast hv)
    linarith
  · refine ⟨_, m6, fun v hv => ?_⟩
    rw [ev_cA]; have := (lXR_le_iff' hg).2 (show (ratPoint v).1 ≤ (ratPoint (I.nxt k)).1 by
      simp only [ratPoint]; exact_mod_cast hv)
    linarith
  · exact ⟨_, m5, by rw [ev_cA]; linarith, by rw [ev_cA]; linarith⟩
  · exact ⟨_, m2, by simp [ArtGallery.det], by simp [ArtGallery.det]⟩
  · exact ⟨_, m3, by rw [ev_cA]; linarith, by rw [ev_cA]; linarith⟩
  · exact ⟨_, m3, by rw [ev_cA]; linarith, by rw [ev_cA]; linarith⟩
  · exact ⟨_, m3, by rw [ev_cA]; linarith, by rw [ev_cA]; linarith⟩
  · exact ⟨_, m4, by simp [ArtGallery.det], by simp [ArtGallery.det]⟩

/-- **The umbra piece lies in the corridor region.** -/
theorem Good.umbra_subset : hpSet (I.umbraFs k) ⊆ I.poly.filled := by
  obtain ⟨c, hc, hcK⟩ := hg.umbra_anchor hk
  exact hpSet_subset_filled hg.poly_simple (hg.umbra_bd hk) hc (hpOpen_subset_hpSet _ hc) hcK.1
    hcK.2

/-- **The nook piece lies in the corridor region** (given one interior point of the corridor in
it). -/
theorem Good.nook_subset {z : Point} (hz : z ∈ hpSet (I.nookFs k)) (hzK : z ∈ I.poly.filled)
    (hzb : z ∉ I.poly.boundary) : hpSet (I.nookFs k) ⊆ I.poly.filled := by
  obtain ⟨l1, l2, r1, r2, hN, hS, hw⟩ := hg.pairR hk
  obtain ⟨e1, e2, e3, e4, e5⟩ := hg.rl_strip_ends hk
  obtain ⟨zx, zy, zξ1, zξ2, zA⟩ := hg.rl_zp hk
  obtain ⟨z1x, z1y⟩ := hg.rl_z1 hk
  obtain ⟨z0x, z0y⟩ := hg.rl_z0 hk
  obtain ⟨n1x, n1y⟩ := hg.rl_n1 hk
  obtain ⟨n0x, n0y⟩ := hg.rl_n0 hk
  have hnx : I.lXR (ratPoint (I.nxt k)) ≤ (I.rwR k - I.lwR k) / 2 - 53 := by
    have := hg.lX_nxt hk
    rw [lXR_ratPoint]; have h' := rat_cast_le_of this; push_cast at h'; simp only [lwR, rwR]
    exact h'
  have hzpp : I.lXR (ratPoint (I.zp k)) < I.lXR (ratPoint (I.sgPt k)) := by
    rw [lXR_ratPoint, lXR_ratPoint]
    exact_mod_cast (fst_lt_iff hg).1 (hg.zp_lt_sgPt hk)
  rw [abs_le] at zx zy n1y n0y
  have hSN : 456 * (N : ℝ) + 1000 ≤ 8 * I.S := by
    obtain ⟨-, -, h1, -⟩ := hg.S_big; linarith
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw2
  -- a strict point: `(X_a, Y_a − 2)`
  set c : Point := ((I.S : ℝ) + 1 + ((I.rwR k - I.lwR k) / 2) / (8 * I.S),
    (I.H : ℝ) + 1 + ((I.lwR k + I.rwR k) / 2 - 2) / (8 * I.S)) with hcdef
  have hSp : (0 : ℝ) < I.S := by rw [hS]; positivity
  have cX : I.lXR c = (I.rwR k - I.lwR k) / 2 := by simp only [lXR, c]; field_simp; ring
  have cY : I.lYR c = (I.lwR k + I.rwR k) / 2 - 2 := by simp only [lYR, c]; field_simp; ring
  have hc : c ∈ hpOpen (I.nookFs k) := by
    simp only [hpOpen, nookFs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, ev_cA, Aff.ev_det, Set.mem_ofPred_eq]
    refine ⟨by rw [cX, z0x]; linarith, by rw [cX, z1x]; linarith, by rw [cY, z1y]; linarith, ?_⟩
    have h64 : (0 : ℝ) < 64 * (I.S : ℝ) ^ 2 := by positivity
    refine pos_of_mul_pos_right ?_ h64.le
    rw [det_lXR, cX, cY, n1x, n0x]
    nlinarith
  have m1 : I.cA 1 0 (-I.lXR (ratPoint (I.z0 k))) ∈ I.nookFs k := by simp [nookFs]
  have m2 : I.cA (-1) 0 (I.lXR (ratPoint (I.z1 k))) ∈ I.nookFs k := by simp [nookFs]
  have m3 : I.cA 0 1 (-I.lYR (ratPoint (I.z1 k))) ∈ I.nookFs k := by simp [nookFs]
  have m4 : Aff.det (ratPoint (I.n1 k)) (ratPoint (I.n0 k)) ∈ I.nookFs k := by simp [nookFs]
  refine hpSet_subset_filled hg.poly_simple ?_ hc hz hzK hzb
  refine hg.bd_check hk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine hg.floor_check m3 ?_
    intro w hw; rw [ev_cA]; have := (lYR_le_floor_iff hg).2 hw; linarith
  · refine ⟨_, m2, ?_, ?_⟩ <;> simp only [ev_cA, lXR_c1', lXR_d1'] <;> linarith
  · refine ⟨_, m1, ?_, ?_⟩ <;> simp only [ev_cA, lXR_c0', lXR_d0'] <;> linarith
  · refine ⟨_, m2, fun v hv => ?_⟩
    rw [ev_cA]; have := (lXR_le_iff' hg).2 (show (ratPoint (I.sgPt k)).1 ≤ (ratPoint v).1 by
      simp only [ratPoint]; exact_mod_cast hv)
    linarith
  · refine ⟨_, m1, fun v hv => ?_⟩
    rw [ev_cA]; have := (lXR_le_iff' hg).2 (show (ratPoint v).1 ≤ (ratPoint (I.nxt k)).1 by
      simp only [ratPoint]; exact_mod_cast hv)
    linarith
  · exact ⟨_, m2, by rw [ev_cA]; linarith, by rw [ev_cA]; linarith⟩
  · exact ⟨_, m2, by rw [ev_cA]; linarith, by rw [ev_cA]; linarith⟩
  · exact ⟨_, m2, by rw [ev_cA]; linarith, by rw [ev_cA, n1x]; linarith⟩
  · exact ⟨_, m4, by simp [ArtGallery.det], by simp [ArtGallery.det]⟩
  · exact ⟨_, m1, by rw [ev_cA, n0x]; linarith, by rw [ev_cA]; linarith⟩
  · exact ⟨_, m1, by rw [ev_cA]; linarith, by rw [ev_cA]; linarith⟩

end Pieces

end Input

end ArtGallery.Sec5.Corridor

end
