module

public import ArtGallery.Hardness.Sec5.Corridor.CoverSlotB

/-!
# Section 5: corridors — the floor slots (visibility and location)

* `Good.sg_sees_slot2`, `Good.sg_sees_slot4`: the stationary guard `p_k` sees every interior point
  of its two slot pieces (the sight segment runs in the slot below the floor line and through the
  strip pieces of the pairs `j ≥ k` above it; docs/section5/08_proof_plan.md §9 (d));
* `Good.classify_lower`: an interior point of the corridor below the floor line lies in a slot
  piece (rays of slopes `2` and `4` downwards from a point outside the slots avoid the boundary).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ}

section SG

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

/-- The stationary guard is at least `1/2` above the floor; its `ζ` is at most `ℓ_k`. -/
theorem Good.sg_facts :
    -(4 * (I.S : ℝ)) ≤ I.lYR (ratPoint (I.sgPt k)) ∧
      I.lYR (ratPoint (I.sgPt k)) - I.lXR (ratPoint (I.sgPt k)) ≤ I.lwR k ∧
      (1 ≤ k → |I.lYR (ratPoint (I.sgPt k))| ≤ 1000 * N) := by
  obtain ⟨hN, hS, hS1, -, hSp, -⟩ := hg.S_big
  obtain ⟨l1, l2, r1, r2, -, -, hw⟩ := hg.pairR hk
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw2
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0
    have hy := hg.lY_sgPt_zero_abs hk
    have h' := rat_cast_le_of hy; push_cast at h'
    rw [← lYR_ratPoint] at h'
    rw [abs_le] at h'
    refine ⟨by nlinarith, ?_, fun h => absurd h (by omega)⟩
    rw [rl_sgPt_zero]; nlinarith
  · obtain ⟨hx, hy⟩ := hg.rl_sgPt hk h0
    have hl := hg.lw_succ (j := k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at hl
    rw [abs_le] at hy
    refine ⟨by nlinarith, by rw [hx]; linarith, fun _ => ?_⟩
    rw [abs_le]; constructor <;> linarith

/-- Deep points (below the floor line, east of `x = S + 3/8`) are inside every left wall. -/
theorem Good.wall_deep {P : Point} (hy1 : -(10 * (I.S : ℝ)) ≤ I.lYR P)
    (hy : I.lYR P ≤ -(8 * I.S)) (hx : -(5 * (I.S : ℝ)) ≤ I.lXR P) (hx2 : I.lXR P ≤ 8 * I.S) :
    0 ≤ ArtGallery.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) P := by
  obtain ⟨hN, hS, hS1, -, hSp, h64⟩ := hg.S_big
  obtain ⟨l1, l2, r1, r2, -, -, hw⟩ := hg.pairR hk
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw2
  obtain ⟨w1, w2⟩ := hg.wall_det hk P
  refine nonneg_of_mul_nonneg_c h64 ?_
  by_cases h : k + 1 < I.np
  · rw [w1 h]; nlinarith
  · rw [w2 h]
    set X0 := (I.rwR k - I.lwR k) / 2 - 3 with hX0d
    set Y0 := (I.lwR k + I.rwR k) / 2 - 3 with hY0d
    have hX0 : |X0| ≤ 456 * N := by rw [abs_le]; constructor <;> linarith
    have hY0 : |Y0| ≤ 500 * N := by rw [abs_le]; constructor <;> nlinarith
    have h1 : |X0 * (I.lYR P - Y0)| ≤ 456 * N * (10 * I.S + 500 * N) := by
      rw [abs_mul]; exact mul_le_mul hX0 (by rw [abs_le] at hY0 ⊢; constructor <;> linarith)
        (abs_nonneg _) (by linarith)
    have h2 : |(I.lXR P - X0) * (24 - Y0)| ≤ (8 * I.S + 456 * N) * (600 * N) := by
      rw [abs_le] at hX0
      rw [abs_mul]; exact mul_le_mul (by rw [abs_le]; constructor <;> linarith)
        (by rw [abs_le] at hY0 ⊢; constructor <;> nlinarith) (abs_nonneg _) (by linarith)
    rw [abs_le] at h1 h2
    have h3 : 8 * (I.S : ℝ) * (3 * I.S) ≤ 8 * I.S * (I.lwR k - (I.lYR P - I.lXR P)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h4 : 456 * (N : ℝ) * (10 * I.S + 500 * N) + (8 * I.S + 456 * N) * (600 * N) <
        8 * I.S * (3 * I.S) := by nlinarith
    linarith

/-- Points east of `z0`, below the line of slope `1/2` through it, are inside the left wall. -/
theorem Good.wall_east {P : Point} (hx : I.lXR (ratPoint (I.z0 k)) ≤ I.lXR P)
    (hy : I.lYR P - I.lYR (ratPoint (I.z0 k)) ≤ (I.lXR P - I.lXR (ratPoint (I.z0 k))) / 2) :
    0 ≤ ArtGallery.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) P := by
  obtain ⟨-, -, hS1, -, hSp, h64⟩ := hg.S_big
  obtain ⟨z0x, z0y⟩ := hg.rl_z0 hk
  obtain ⟨n1, n2⟩ := hg.rl_nxt hk
  obtain ⟨l1, l2, r1, r2, hN, -, hw⟩ := hg.pairR hk
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw2
  refine nonneg_of_mul_nonneg_c h64 ?_
  rw [det_lXR]
  have hab : 0 ≤ I.lXR (ratPoint (I.z0 k)) - I.lXR (ratPoint (I.nxt k)) ∧
      (I.lXR (ratPoint (I.z0 k)) - I.lXR (ratPoint (I.nxt k))) / 2 ≤
        I.lYR (ratPoint (I.z0 k)) - I.lYR (ratPoint (I.nxt k)) := by
    rw [z0x, z0y]
    by_cases h : k + 1 < I.np
    · rw [(n1 h).1, (n1 h).2]; constructor <;> linarith
    · rw [(n2 h).1, (n2 h).2]; constructor <;> nlinarith
  obtain ⟨ha, hb⟩ := hab
  have hX : 0 ≤ I.lXR P - I.lXR (ratPoint (I.z0 k)) := by linarith
  set a := I.lXR (ratPoint (I.z0 k)) - I.lXR (ratPoint (I.nxt k))
  set b := I.lYR (ratPoint (I.z0 k)) - I.lYR (ratPoint (I.nxt k))
  have e : (I.lXR (ratPoint (I.nxt k)) - I.lXR (ratPoint (I.z0 k))) *
      (I.lYR P - I.lYR (ratPoint (I.z0 k))) - (I.lXR P - I.lXR (ratPoint (I.z0 k))) *
      (I.lYR (ratPoint (I.nxt k)) - I.lYR (ratPoint (I.z0 k))) =
      -a * (I.lYR P - I.lYR (ratPoint (I.z0 k))) + b * (I.lXR P - I.lXR (ratPoint (I.z0 k))) := by
    simp only [a, b]; ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hy ha, mul_le_mul_of_nonneg_right hb hX]

/-- Deep points are below every axis. -/
theorem Good.AR_deep {P : Point} (hy : I.lYR P ≤ -(8 * I.S)) (hx : |I.lXR P| ≤ 8 * I.S) :
    I.AR k P < 0 := by
  obtain ⟨E, hE, hEb⟩ := hg.AR_eq hk P
  obtain ⟨hD1, -⟩ := hg.DDR_bounds hk
  have hh := hg.hhR_abs hk
  obtain ⟨hN, hS, hS1, -, hSp, -⟩ := hg.S_big
  obtain ⟨l1, l2, r1, r2, -, -, hw⟩ := hg.pairR hk
  rw [abs_le] at hEb hh
  have hhX : |((I.hh k : ℚ) : ℝ) * I.lXR P| ≤ (3 * N + 50) * (8 * I.S) := by
    rw [abs_mul]; exact mul_le_mul (abs_le.2 hh) hx (abs_nonneg _) (by linarith)
  rw [abs_le] at hhX
  have hf : I.lYR P - ((I.lwR k + I.rwR k) / 2 - 16) ≤ -(7 * (I.S : ℝ)) := by nlinarith
  have h7 : ((I.DD k : ℚ) : ℝ) * (I.lYR P - ((I.lwR k + I.rwR k) / 2 - 16)) ≤
      (I.S : ℝ) * (-(7 * I.S)) :=
    (mul_le_mul_of_nonpos_right hD1 (by linarith)).trans (mul_le_mul_of_nonneg_left hf hSp.le)
  have h9 : (3 * (N : ℝ) + 50) * (8 * I.S) + 4 * (17 * N + 100) * (14 * N + 50) <
      (I.S : ℝ) * (7 * I.S) := by nlinarith
  rw [hE]; linarith

/-- The part above the floor line of a sight segment of `p_k` towards a deep point. -/
theorem Good.sg_seg_upper {z s : Point}
    (hzy1 : -(10 * (I.S : ℝ)) ≤ I.lYR z) (hzy : I.lYR z ≤ -(8 * I.S))
    (hzx : -(5 * (I.S : ℝ)) ≤ I.lXR z) (hzp : I.lXR z ≤ I.lXR (ratPoint (I.sgPt k)))
    (hζ : I.lYR z - I.lXR z ≤ I.lYR (ratPoint (I.sgPt k)) - I.lXR (ratPoint (I.sgPt k)))
    (hs : s ∈ ArtGallery.segment (ratPoint (I.sgPt k)) z) (hsH : -(8 * (I.S : ℝ)) ≤ I.lYR s) :
    s ∈ I.poly.filled := by
  obtain ⟨y1, ζp, yw⟩ := hg.sg_facts hk
  obtain ⟨e1, e2, e3, e4, e5⟩ := hg.rl_strip_ends hk
  obtain ⟨hN, hS, hS1, -, hSp, h64⟩ := hg.S_big
  have hpS := hg.sgPt_mem_strip hk
  rw [mem_strip_iff] at hpS
  obtain ⟨-, -, -, hpA, hpW⟩ := hpS
  set p := ratPoint (I.sgPt k)
  -- coordinates along the segment
  have hconv : ∀ f : Aff, ∀ c : ℝ, c ≤ f.ev p → c ≤ f.ev z → c ≤ f.ev s :=
    fun f c h1 h2 => f.ge_ev_of_segment hs h1 h2
  have hconv' : ∀ f : Aff, ∀ c : ℝ, f.ev p ≤ c → f.ev z ≤ c → f.ev s ≤ c :=
    fun f c h1 h2 => f.ev_le_of_segment hs h1 h2
  have hsx : I.lXR s ≤ I.lXR p := by
    have := hconv' (I.cA 1 0 0) (I.lXR p) (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
    rw [ev_cA] at this; linarith
  have hsx' : -(8 * (I.S : ℝ)) ≤ I.lXR s := by
    have := hconv (I.cA 1 0 0) (-(8 * I.S)) (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
    rw [ev_cA] at this; linarith
  have hsζ : I.lYR s - I.lXR s ≤ I.lwR k := by
    have := hconv' (I.cA (-1) 1 0) (I.lwR k) (by rw [ev_cA]; linarith) (by rw [ev_cA]; linarith)
    rw [ev_cA] at this; linarith
  have hzW : ∀ j < I.np, 0 ≤ ArtGallery.det (ratPoint (I.z0 j)) (ratPoint (I.nxt j)) z :=
    fun j hj => hg.wall_deep hj hzy1 hzy hzx (by linarith)
  obtain ⟨j, hkj, hj, hj1, hj2⟩ := hg.strip_west hk hsx' hsx
  rcases hkj.lt_or_eq with hkj | rfl
  · refine hg.west_point hk hkj hj hj1 hj2 hsH hsζ fun hlast => ?_
    -- the last wall: convexity between `p_k` and `z`
    have hpW' : 0 ≤ ArtGallery.det (ratPoint (I.z0 j)) (ratPoint (I.nxt j)) p := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0
        obtain ⟨z0x, z0y⟩ := hg.rl_z0 hj
        obtain ⟨-, -, -, -, -, -, hwj⟩ := hg.pairR hj
        have hwj2 : |(I.rwR j - I.lwR j) / 2| ≤ 456 * N - 20 := by linarith
        have hy0 := hg.lY_sgPt_zero_abs hk
        have h' := rat_cast_le_of hy0; push_cast at h'
        rw [← lYR_ratPoint] at h'
        have hlj := (hg.pairR hj).1
        have hlj2 := (hg.pairR hj).2.1
        have hrj := (hg.pairR hj).2.2.1
        have hrj2 := (hg.pairR hj).2.2.2.1
        rw [abs_le] at hwj2 h'
        refine hg.wall_east hj (by rw [z0x, rl_sgPt_zero]; linarith) ?_
        rw [z0x, z0y, rl_sgPt_zero]; nlinarith
      · have hlm := hg.lw_mono (show k + 1 ≤ j by omega) hj
        have hls := hg.lw_succ (j := k) (by omega)
        exact (hg.wall_of_window hj (e4 h0 |>.trans (by linarith))
          (yw h0 |>.trans (by linarith)) (by linarith)).le
    have := Aff.ge_ev_of_segment (Aff.det (ratPoint (I.z0 j)) (ratPoint (I.nxt j))) hs (c := 0)
      (by rw [Aff.ev_det]; exact hpW') (by rw [Aff.ev_det]; exact hzW j hj)
    rwa [Aff.ev_det] at this
  · refine hg.strip_subset hk ?_
    rw [mem_strip_iff]
    refine ⟨hj2, hj1, hsH, ?_, ?_⟩
    · have hzA := hg.AR_deep hk hzy (by rw [abs_le]; constructor <;> linarith)
      have := (I.cA (-((I.hh k : ℚ) : ℝ)) ((I.DD k : ℚ) : ℝ)
        (-(8 * I.S * ((I.gg k : ℚ) : ℝ)))).ev_le_of_segment hs (c := 0)
        (by rw [← AR_eq_cA]; exact hpA) (by rw [← AR_eq_cA]; exact hzA.le)
      rwa [← AR_eq_cA] at this
    · have := Aff.ge_ev_of_segment (Aff.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k))) hs (c := 0)
        (by rw [Aff.ev_det]; exact hpW) (by rw [Aff.ev_det]; exact hzW k hk)
      rwa [Aff.ev_det] at this

omit hk in
/-- Conditions of `Good.sg_seg_upper` from coordinates relative to the floor line. -/
theorem Good.sg_upper_conds (_hk : k < I.np) {z : Point} (hzy1 : -(1 / 4 : ℝ) ≤ z.2 - I.H)
    (hzy : z.2 ≤ I.H)
    (hzx : (I.S : ℝ) + 3 / 8 ≤ z.1) (hzp : z.1 ≤ ((I.sgPt k).1 : ℝ))
    (hζ : z.2 - z.1 ≤ ((I.sgPt k).2 : ℝ) - (I.sgPt k).1) :
    -(10 * (I.S : ℝ)) ≤ I.lYR z ∧ I.lYR z ≤ -(8 * I.S) ∧ -(5 * (I.S : ℝ)) ≤ I.lXR z ∧
      I.lXR z ≤ I.lXR (ratPoint (I.sgPt k)) ∧
      I.lYR z - I.lXR z ≤ I.lYR (ratPoint (I.sgPt k)) - I.lXR (ratPoint (I.sgPt k)) := by
  have hS : (0 : ℝ) ≤ 8 * I.S := by have := hg.S_pos; positivity
  have a1 := mul_le_mul_of_nonneg_left hzy1 hS
  have a2 := mul_le_mul_of_nonneg_left hzy hS
  have a3 := mul_le_mul_of_nonneg_left hzx hS
  have a4 := mul_le_mul_of_nonneg_left hzp hS
  have a5 := mul_le_mul_of_nonneg_left hζ hS
  simp only [lXR, lYR, ratPoint_fst, ratPoint_snd]
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **The stationary guard sees its slope-2 slot piece** (interior points of the corridor). -/
theorem Good.sg_sees_slot2 {P : Polygon} (hsub : I.poly.filled ⊆ P.filled) {z : Point}
    (hz : z ∈ hpSet (I.slot2Fs k)) (hzK : z ∈ I.poly.filled) (hzb : z ∉ I.poly.boundary) :
    P.Sees (ratPoint (I.sgPt k)) z := by
  have hpc := hg.slot2_subset hk hz hzK hzb
  obtain ⟨he, he1⟩ := hg.eps_real
  obtain ⟨h1, h2⟩ := hg.sgPt_height hk
  have hp2 := sgPt_on_slot2 (I := I) k
  have k2 := hg.kx2_real hk
  have hz' := hz
  rw [mem_slot2_iff] at hz'
  obtain ⟨z1, z2, z3⟩ := hz'
  have ht : -(1 / 8 : ℝ) ≤ z.2 - I.H := by
    by_contra hc
    have : (I.ε : ℝ) * (z.2 - I.H + 1 / 8) < 0 := mul_neg_of_pos_of_neg he (by linarith)
    linarith
  have hε : (I.ε : ℝ) * (z.2 - I.H + 1 / 8) ≤ (I.ε : ℝ) / 8 := by nlinarith
  intro s hs
  apply hsub
  by_cases hsH : s.2 ≤ I.H
  · apply hpc
    intro f hf
    simp only [slot2Fs, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · simp only [Aff.ev]; linarith
    · refine Aff.ge_ev_of_segment _ hs (c := 0) ?_ (hz _ (by simp [slot2Fs]))
      simp only [Aff.ev, ratPoint_fst, ratPoint_snd]; linarith
    · refine Aff.ge_ev_of_segment _ hs (c := 0) ?_ (hz _ (by simp [slot2Fs]))
      have := mul_pos he (show (0 : ℝ) < ((I.sgPt k).2 : ℝ) - I.H + 1 / 8 by linarith)
      simp only [Aff.ev, ratPoint_fst, ratPoint_snd]; linarith
  · obtain ⟨c1, c2, c3, c4, c5⟩ := hg.sg_upper_conds hk (z := z) (by linarith) z1
      (by linarith) (by linarith) (by linarith)
    refine hg.sg_seg_upper hk c1 c2 c3 c4 c5 hs ?_
    have := (lYR_le_floor_iff hg (p := s)).not.2 hsH
    linarith

/-- **The stationary guard sees its slope-4 slot piece** (interior points of the corridor). -/
theorem Good.sg_sees_slot4 {P : Polygon} (hsub : I.poly.filled ⊆ P.filled) {z : Point}
    (hz : z ∈ hpSet (I.slot4Fs k)) (hzK : z ∈ I.poly.filled) (hzb : z ∉ I.poly.boundary) :
    P.Sees (ratPoint (I.sgPt k)) z := by
  have hpc := hg.slot4_subset hk hz hzK hzb
  obtain ⟨he, he1⟩ := hg.eps_real
  obtain ⟨h1, h2⟩ := hg.sgPt_height hk
  have hp4 := sgPt_on_slot4 (I := I) k
  have k4 := hg.kx4_real hk
  have hz' := hz
  rw [mem_slot4_iff] at hz'
  obtain ⟨z1, z2, z3⟩ := hz'
  have ht : -(1 / 4 : ℝ) ≤ z.2 - I.H := by
    by_contra hc
    have : (I.ε : ℝ) / 2 * (z.2 - I.H + 1 / 4) < 0 := mul_neg_of_pos_of_neg (by linarith)
      (by linarith)
    linarith
  have hε : (I.ε : ℝ) / 2 * (z.2 - I.H + 1 / 4) ≤ (I.ε : ℝ) / 8 := by nlinarith
  intro s hs
  apply hsub
  by_cases hsH : s.2 ≤ I.H
  · apply hpc
    intro f hf
    simp only [slot4Fs, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · simp only [Aff.ev]; linarith
    · refine Aff.ge_ev_of_segment _ hs (c := 0) ?_ (hz _ (by simp [slot4Fs]))
      simp only [Aff.ev, ratPoint_fst, ratPoint_snd]; linarith
    · refine Aff.ge_ev_of_segment _ hs (c := 0) ?_ (hz _ (by simp [slot4Fs]))
      have := mul_pos (half_pos he)
        (show (0 : ℝ) < ((I.sgPt k).2 : ℝ) - I.H + 1 / 4 by linarith)
      simp only [Aff.ev, ratPoint_fst, ratPoint_snd]; linarith
  · obtain ⟨c1, c2, c3, c4, c5⟩ := hg.sg_upper_conds hk (z := z) ht z1
      (by linarith) (by linarith) (by linarith)
    refine hg.sg_seg_upper hk c1 c2 c3 c4 c5 hs ?_
    have := (lYR_le_floor_iff hg (p := s)).not.2 hsH
    linarith

end SG

end Input

end ArtGallery.Sec5.Corridor

end
