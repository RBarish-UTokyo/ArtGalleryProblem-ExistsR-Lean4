module

public import ArtGallery.Hardness.Sec5.Corridor.Visibility
public import ArtGallery.Vis.StationaryGuard

/-!
# Section 5: corridors — the stationary guards

For every pair `k`, the stationary guard `p_k` is the only point seeing both tips of its floor
witness slots (`Good.sg_unique`, via `Polygon.sg_unique_of_vertices`):

* `p_k` is the vertex of `P` between the vertical edge `base_k → p_k` and the axis edge
  `p_k → z'_k`;
* the tip `q_a` of the slope-2 slot and the tip `q_b` of the slope-4 slot are convex vertices of
  `P`; their cones are the thin wedges between the slot sides, the cone of `q_a` lying right of
  the line `p_k q_a` and that of `q_b` left of `p_k q_b`.

With `p_k = (p_x, p_y)`, `h = p_y − H`, the slots are `q_a = p_k − α(1, 2)`, `q_b = p_k − β(1, 4)`
(`α = h/2 + 1/16`, `β = h/4 + 1/16`), and all hypotheses of `sg_unique_of_vertices` are explicit
polynomial identities (`sg_dets`) in `p_x − z'_x`, `p_y − base_y`, the axis slope `m`, `α`, `β` and
`ε`.

Index bookkeeping: `chainAfter_infix_sg`, `chainBefore_infix_slot2/4`, `CorridorAt.vtx_*`.
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

/-! ## The determinant conditions -/

section Dets

variable {px py uy wx H e m : ℚ}

/-- The stationary-guard configuration of a pair, in coordinates. -/
structure SGConfig (px py uy wx H e m : ℚ) : Prop where
  he : 0 < e
  he1 : e ≤ 1 / 1000
  hm : |m| ≤ 1 / 1000
  hpw : 37 * e ≤ px - wx
  hpu : 37 * e ≤ py - uy
  huH : uy - H ≤ 3 / 2
  hh1 : 1 / 2 ≤ py - H
  hh2 : py - H ≤ 3 / 2

/-- All determinant conditions of the stationary-guard lemma. -/
theorem SGConfig.dets (h : SGConfig px py uy wx H e m) :
    let p : ℚ × ℚ := (px, py)
    let u : ℚ × ℚ := (px, uy)
    let w : ℚ × ℚ := (wx, py + m * (wx - px))
    let k2 := px - (py - H) / 2
    let k4 := px - (py - H) / 4
    let qa : ℚ × ℚ := (k2 - 1 / 16, H - 2 / 16)
    let ua : ℚ × ℚ := (k2 - e / 8, H)
    let wa : ℚ × ℚ := (k2, H)
    let qb : ℚ × ℚ := (k4 - 1 / 16, H - 4 / 16)
    let ub : ℚ × ℚ := (k4, H)
    let wb : ℚ × ℚ := (k4 + e / 8, H)
    0 < det2 ua qa wa ∧ 0 < det2 ub qb wb ∧ 0 < det2 p w qa ∧ 0 < det2 p w qb ∧
      0 < det2 u p qa ∧ 0 < det2 u p qb ∧ 0 < det2 p qa qb ∧ 0 ≤ det2 qa p ua ∧
      0 ≤ det2 qa p wa ∧ 0 ≤ det2 p qb ub ∧ 0 ≤ det2 p qb wb ∧ det2 qa w ua < 0 ∧
      det2 qa w wa < 0 ∧ 0 < det2 qb u ub ∧ 0 < det2 qb u wb := by
  obtain ⟨he, he1, hm, hpw, hpu, huH, hh1, hh2⟩ := h
  rw [abs_le] at hm
  intro p u w k2 k4 qa ua wa qb ub wb
  have hα : 0 < (py - H) / 2 + 1 / 16 := by linarith
  have hβ : 0 < (py - H) / 4 + 1 / 16 := by linarith
  have hpw' : 0 < px - wx := by linarith
  have hpu' : 0 < py - uy := by linarith
  simp only [p, u, w, k2, k4, qa, ua, wa, qb, ub, wb, det2]
  refine ⟨by nlinarith, by nlinarith, ?_, ?_, ?_, ?_, ?_, ?_, le_of_eq (by ring), le_of_eq (by ring),
    ?_, ?_, ?_, ?_, ?_⟩
  · have e1 : (wx - px) * (H - 2 / 16 - py) - (px - (py - H) / 2 - 1 / 16 - px) *
        (py + m * (wx - px) - py) = ((py - H) / 2 + 1 / 16) * (px - wx) * (2 - m) := by ring
    rw [e1]; apply mul_pos (mul_pos hα hpw'); linarith
  · have e1 : (wx - px) * (H - 4 / 16 - py) - (px - (py - H) / 4 - 1 / 16 - px) *
        (py + m * (wx - px) - py) = ((py - H) / 4 + 1 / 16) * (px - wx) * (4 - m) := by ring
    rw [e1]; apply mul_pos (mul_pos hβ hpw'); linarith
  · have e1 : (px - px) * (H - 2 / 16 - uy) - (px - (py - H) / 2 - 1 / 16 - px) * (py - uy) =
        ((py - H) / 2 + 1 / 16) * (py - uy) := by ring
    rw [e1]; positivity
  · have e1 : (px - px) * (H - 4 / 16 - uy) - (px - (py - H) / 4 - 1 / 16 - px) * (py - uy) =
        ((py - H) / 4 + 1 / 16) * (py - uy) := by ring
    rw [e1]; positivity
  · have e1 : (px - (py - H) / 2 - 1 / 16 - px) * (H - 4 / 16 - py) -
        (px - (py - H) / 4 - 1 / 16 - px) * (H - 2 / 16 - py) =
        2 * ((py - H) / 2 + 1 / 16) * ((py - H) / 4 + 1 / 16) := by ring
    rw [e1]; positivity
  · have e1 : (px - (px - (py - H) / 2 - 1 / 16)) * (H - (H - 2 / 16)) -
        (px - (py - H) / 2 - e / 8 - (px - (py - H) / 2 - 1 / 16)) * (py - (H - 2 / 16)) =
        ((py - H) / 2 + 1 / 16) * e / 4 := by ring
    rw [e1]; positivity
  · have e1 : (px - (py - H) / 4 - 1 / 16 - px) * (H - py) -
        (px - (py - H) / 4 + e / 8 - px) * (H - 4 / 16 - py) =
        ((py - H) / 4 + 1 / 16) * e / 2 := by ring
    rw [e1]; positivity
  · have e1 : (wx - (px - (py - H) / 2 - 1 / 16)) * (H - (H - 2 / 16)) -
        (px - (py - H) / 2 - e / 8 - (px - (py - H) / 2 - 1 / 16)) *
          (py + m * (wx - px) - (H - 2 / 16)) =
        -(px - wx) * (1 / 8 - m / 16 + m * e / 8) + ((py - H) / 2 + 1 / 16) * e / 4 := by ring
    rw [e1]
    have : 1 / 8 - m / 16 + m * e / 8 ≥ 1 / 9 := by nlinarith
    nlinarith
  · have e1 : (wx - (px - (py - H) / 2 - 1 / 16)) * (H - (H - 2 / 16)) -
        (px - (py - H) / 2 - (px - (py - H) / 2 - 1 / 16)) *
          (py + m * (wx - px) - (H - 2 / 16)) = -(px - wx) * (1 / 8 - m / 16) := by ring
    rw [e1]
    have : 0 < 1 / 8 - m / 16 := by linarith
    nlinarith
  · have e1 : (px - (px - (py - H) / 4 - 1 / 16)) * (H - (H - 4 / 16)) -
        (px - (py - H) / 4 - (px - (py - H) / 4 - 1 / 16)) * (uy - (H - 4 / 16)) =
        (py - uy) / 16 := by ring
    rw [e1]; positivity
  · have e1 : (px - (px - (py - H) / 4 - 1 / 16)) * (H - (H - 4 / 16)) -
        (px - (py - H) / 4 + e / 8 - (px - (py - H) / 4 - 1 / 16)) * (uy - (H - 4 / 16)) =
        (py - uy) / 16 - (uy - H + 1 / 4) * e / 8 := by ring
    rw [e1]
    nlinarith

/-- The determinant conditions for named points. -/
theorem SGConfig.dets' (h : SGConfig px py uy wx H e m) {p u w qa ua wa qb ub wb : ℚ × ℚ}
    (hp : p = (px, py)) (hu : u = (px, uy)) (hw : w = (wx, py + m * (wx - px)))
    (hqa : qa = (px - (py - H) / 2 - 1 / 16, H - 2 / 16)) (hua : ua = (px - (py - H) / 2 - e / 8, H))
    (hwa : wa = (px - (py - H) / 2, H)) (hqb : qb = (px - (py - H) / 4 - 1 / 16, H - 4 / 16))
    (hub : ub = (px - (py - H) / 4, H)) (hwb : wb = (px - (py - H) / 4 + e / 8, H)) :
    0 < det2 ua qa wa ∧ 0 < det2 ub qb wb ∧ 0 < det2 p w qa ∧ 0 < det2 p w qb ∧
      0 < det2 u p qa ∧ 0 < det2 u p qb ∧ 0 < det2 p qa qb ∧ 0 ≤ det2 qa p ua ∧
      0 ≤ det2 qa p wa ∧ 0 ≤ det2 p qb ub ∧ 0 ≤ det2 p qb wb ∧ det2 qa w ua < 0 ∧
      det2 qa w wa < 0 ∧ 0 < det2 qb u ub ∧ 0 < det2 qb u wb := by
  subst hp hu hw hqa hua hwa hqb hub hwb
  exact h.dets

end Dets

/-! ## Index bookkeeping -/

/-- In a chain at index `a` of `P` written as `L₁ ++ [x, y, z] ++ L₂`, the vertex `y` has index
`(a + |L₁| + 1) % n` with neighbours `x`, `z`. -/
theorem vtx_triple {P : Polygon} {L L₁ L₂ : List (ℚ × ℚ)} {x y z : ℚ × ℚ} {a : ℕ}
    (hn : 0 < P.n) (hch : ∀ j < L.length, P.vtx ((a + j) % P.n) = ratPoint (L.getD j 0))
    (hL : L = L₁ ++ [x, y, z] ++ L₂) :
    P.vtx ((a + L₁.length + 1) % P.n) = ratPoint y ∧
      P.vtx (((a + L₁.length + 1) % P.n + P.n - 1) % P.n) = ratPoint x ∧
      P.vtx (((a + L₁.length + 1) % P.n + 1) % P.n) = ratPoint z ∧
      P.vtx ((a + L₁.length) % P.n) = ratPoint x ∧
      P.vtx (((a + L₁.length) % P.n + 1) % P.n) = ratPoint y := by
  have hlen : L.length = L₁.length + 3 + L₂.length := by rw [hL]; simp; omega
  have g : ∀ i, i < 3 → L.getD (L₁.length + i) 0 = [x, y, z].getD i 0 := by
    intro i hi
    rw [hL, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.append_assoc,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by simpa using hi)]
  have v0 := hch (L₁.length) (by omega)
  have v1 := hch (L₁.length + 1) (by omega)
  have v2 := hch (L₁.length + 2) (by omega)
  have g0 := g 0 (by norm_num)
  rw [Nat.add_zero] at g0
  rw [g0] at v0
  rw [g 1 (by norm_num)] at v1
  rw [g 2 (by norm_num)] at v2
  simp only [List.getD_cons_zero, List.getD_cons_succ] at v0 v1 v2
  refine ⟨by rw [Nat.add_assoc, v1], ?_, ?_, by rw [← v0], ?_⟩
  · have := chain_prev (Q := P) hn a (j := L₁.length + 1) (by omega)
    unfold Jordan.prevIdx at this
    rw [Nat.add_assoc, this, Nat.add_sub_cancel, v0]
  · rw [Nat.add_assoc, chain_succ, Nat.add_assoc, v2]
  · rw [chain_succ, v1]

/-- Membership in a list as a decomposition. -/
theorem exists_split_of_mem {α : Type*} {l : List α} {x : α} (h : x ∈ l) :
    ∃ s t, l = s ++ x :: t := List.append_of_mem h

namespace Input

variable {I : Input} {N : ℚ}

/-- The edges `base_k → p_k → z'_k` are consecutive in the upper wall. -/
theorem chainAfter_infix_sg {k : ℕ} (hk : k < I.np) :
    ∃ L₁ L₂, I.chainAfter = L₁ ++ [I.base k, I.sgPt k, I.zp k] ++ L₂ := by
  obtain ⟨s, t, hst⟩ := exists_split_of_mem (List.mem_range.2 hk)
  have hu : I.upper = s.flatMap I.upperPair ++ I.upperPair k ++ t.flatMap I.upperPair := by
    rw [upper, hst, List.flatMap_append, List.flatMap_cons, List.append_assoc]
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · refine ⟨[], [I.z1 0, I.n1 0, I.n0 0, I.z0 0] ++ (s.flatMap I.upperPair ++ []) ++
      t.flatMap I.upperPair ++ [d0 I.S I.H], ?_⟩
    -- `s` is empty since `0` is the first element of `range`
    have hs : s = [] := by
      cases s with
      | nil => rfl
      | cons x s =>
        exfalso
        have h0 : (List.range I.np)[0]? = some x := by rw [hst]; simp
        rw [List.getElem?_range (by omega)] at h0
        simp only [Option.some.injEq] at h0
        subst h0
        have hnd := List.nodup_range (n := I.np)
        rw [hst] at hnd
        simp at hnd
    subst hs
    simp [chainAfter, hu, upperPair, base]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    refine ⟨[d1 I.S I.H] ++ s.flatMap I.upperPair, [I.z1 (j + 1), I.n1 (j + 1), I.n0 (j + 1),
      I.z0 (j + 1)] ++ t.flatMap I.upperPair ++ [d0 I.S I.H], ?_⟩
    rw [chainAfter, hu, upperPair_succ]
    simp [base]

/-- The slope-2 slot of pair `k` is a contiguous part of the floor chain. -/
theorem chainBefore_infix_slot2 {k : ℕ} (hk : k < I.np) :
    ∃ L₁ L₂, I.chainBefore = L₁ ++ I.slot2 k ++ L₂ := by
  have hmem : I.e2 k ∈ I.floorEntries.mergeSort (fun a b => decide (a.1 ≤ b.1)) := by
    rw [(List.mergeSort_perm _ _).mem_iff]
    simp only [floorEntries, List.mem_flatMap, List.mem_range, List.mem_cons]
    exact ⟨k, hk, Or.inl rfl⟩
  obtain ⟨s, t, hst⟩ := exists_split_of_mem hmem
  refine ⟨[c0 I.S I.H] ++ s.flatMap (·.2), t.flatMap (·.2) ++ [c1 I.S I.H], ?_⟩
  simp [chainBefore, floor, hst, e2]

/-- The slope-4 slot of pair `k` is a contiguous part of the floor chain. -/
theorem chainBefore_infix_slot4 {k : ℕ} (hk : k < I.np) :
    ∃ L₁ L₂, I.chainBefore = L₁ ++ I.slot4 k ++ L₂ := by
  have hmem : I.e4 k ∈ I.floorEntries.mergeSort (fun a b => decide (a.1 ≤ b.1)) := by
    rw [(List.mergeSort_perm _ _).mem_iff]
    simp only [floorEntries, List.mem_flatMap, List.mem_range, List.mem_cons]
    exact ⟨k, hk, Or.inr (Or.inl rfl)⟩
  obtain ⟨s, t, hst⟩ := exists_split_of_mem hmem
  refine ⟨[c0 I.S I.H] ++ s.flatMap (·.2), t.flatMap (·.2) ++ [c1 I.S I.H], ?_⟩
  simp [chainBefore, floor, hst, e4]

/-! ## The configuration of a pair -/

section Config

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

/-- The axis edge of pair `k` in coordinates: `z'_y = p_y + m (z'_x − p_x)` with `m = h/D`. -/
theorem Good.zp_on_axis :
    (I.zp k).2 = (I.sgPt k).2 + I.hh k / I.DD k * ((I.zp k).1 - (I.sgPt k).1) := by
  have hD := hg.DD_pos hk
  have hS := hg.S_pos
  rw [show I.zp k = I.onUmbra k (I.zp k).1 from rfl, show I.sgPt k = I.onUmbra k (I.sgPt k).1
    from rfl, onUmbra_snd hg hk, onUmbra_snd hg hk, onUmbra_fst', onUmbra_fst']
  field_simp
  ring

theorem Good.slope_small : |I.hh k / I.DD k| ≤ 1 / 1000 := by
  have hD := hg.DD_pos hk
  have hS := hg.S_pos
  have h1 := hg.hh_abs hk
  have hN := hg.N_ge
  have hSe := hg.S_eq
  rw [abs_div, abs_of_pos (a := I.DD k) (by linarith), div_le_iff₀ (by linarith)]
  rw [abs_le] at h1 ⊢
  constructor <;> nlinarith

/-- **The stationary-guard configuration** of pair `k`. -/
theorem Good.sgConfig : SGConfig (I.sgPt k).1 (I.sgPt k).2 (I.base k).2 (I.zp k).1 I.H I.ε
    (I.hh k / I.DD k) := by
  have hS := hg.S_pos
  have hSe := hg.S_eq
  have hN := hg.N_ge
  have hS8 := hg.scale.S_ge
  obtain ⟨he, he1⟩ := eps_small hg
  have hzp := hg.lX_zp hk
  rw [abs_le] at hzp
  have hεdef : I.ε = 1 / (8 * I.S) := rfl
  -- local coordinates
  have epx := fst_eq_of_lX hg (I.sgPt k)
  have epy := snd_eq_of_lY hg (I.sgPt k)
  have ewx := fst_eq_of_lX hg (I.zp k)
  have euy := snd_eq_of_lY hg (I.base k)
  have k1 : 37 * I.ε ≤ (I.sgPt k).1 - (I.zp k).1 := by
    have := hg.zp_lt_sgPt hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have hlx := lX_sgPt_zero (I := I)
      rw [epx, ewx, hlx, hεdef]
      have := hg.window_apex hk
      have hab := abs_nonneg ((I.rwE 0 - I.lwE 0) / 2)
      rw [show I.S + 1 + 8 * I.S / (8 * I.S) - (I.S + 1 + I.lX (I.zp 0) / (8 * I.S)) =
        (8 * I.S - I.lX (I.zp 0)) / (8 * I.S) by field_simp; ring,
        show 37 * (1 / (8 * I.S)) = 37 / (8 * I.S) by ring]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rcases abs_cases ((I.rwE 0 - I.lwE 0) / 2) with ⟨h, _⟩ | ⟨h, _⟩ <;> nlinarith
    · rw [epx, ewx, lX_sgPt hg hk hk1, hεdef]
      have := hg.lwE_succ (k := k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at this
      rw [show I.S + 1 + ((I.rwE k - I.lwE (k - 1)) / 2 + 1 / 4) / (8 * I.S) -
          (I.S + 1 + I.lX (I.zp k) / (8 * I.S)) =
          ((I.rwE k - I.lwE (k - 1)) / 2 + 1 / 4 - I.lX (I.zp k)) / (8 * I.S) by field_simp; ring,
        show 37 * (1 / (8 * I.S)) = 37 / (8 * I.S) by ring]
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
  have k2 : 37 * I.ε ≤ (I.sgPt k).2 - (I.base k).2 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [base_zero, epy, hεdef]
      have hb := hg.lY_sgPt_zero_abs (by omega)
      rw [abs_le] at hb
      have : (d1 I.S I.H).2 = I.H + 3 / (2 * I.S) := by simp [d1, rho]
      rw [this, show I.H + 1 + I.lY (I.sgPt 0) / (8 * I.S) - (I.H + 3 / (2 * I.S)) =
        (8 * I.S + I.lY (I.sgPt 0) - 12) / (8 * I.S) by field_simp; ring,
        show 37 * (1 / (8 * I.S)) = 37 / (8 * I.S) by ring]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    · rw [show I.base k = I.valley k by simp [base, show k ≠ 0 by omega], epy,
        snd_eq_of_lY hg (I.valley k), lY_valley hg hk, hεdef]
      have h1 := hg.lY_sgPt hk hk1
      have h2 := hg.lwE_succ (k := k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at h2
      rw [abs_le] at h1
      rw [show I.H + 1 + I.lY (I.sgPt k) / (8 * I.S) -
          (I.H + 1 + ((I.rwE k + I.lwE (k - 1)) / 2 + 1 / 4) / (8 * I.S)) =
          (I.lY (I.sgPt k) - ((I.rwE k + I.lwE (k - 1)) / 2 + 1 / 4)) / (8 * I.S) by
            field_simp; ring,
        show 37 * (1 / (8 * I.S)) = 37 / (8 * I.S) by ring]
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
  -- heights of `p_k` and `base_k`
  have hpy : |I.lY (I.sgPt k)| ≤ 8 * (20 * N + 150) + 68 * N + 400 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have := hg.lY_sgPt_zero_abs (by omega); nlinarith [abs_nonneg (I.lY (I.sgPt 0))]
    · have := hg.lY_sgPt_abs hk hk1; nlinarith [abs_nonneg (I.lY (I.sgPt k))]
  have hpy' : |I.lY (I.sgPt k) / (8 * I.S)| ≤ 1 / 4 := by
    rw [abs_div, abs_of_pos (a := 8 * I.S) (by linarith), div_le_iff₀ (by linarith)]; nlinarith
  rw [abs_le] at hpy'
  have huy : (I.base k).2 - I.H ≤ 3 / 2 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [base_zero]; simp only [d1, rho]
      have : 3 / (2 * I.S) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      linarith
    · rw [show I.base k = I.valley k by simp [base, show k ≠ 0 by omega],
        snd_eq_of_lY hg (I.valley k)]
      have := (hg.feature_valley hk hk1).2
      have h' : |I.lY (I.valley k) / (8 * I.S)| ≤ 1 / 4 := by
        rw [abs_div, abs_of_pos (a := 8 * I.S) (by linarith), div_le_iff₀ (by linarith)]; nlinarith
      rw [abs_le] at h'
      linarith
  exact ⟨he, by linarith, hg.slope_small hk, k1, k2, huy, by rw [epy]; linarith,
    by rw [epy]; linarith⟩

end Config

/-! ## The stationary-guard lemma -/

section SG

variable (hg : I.Good N) {P : Polygon} {a b : ℕ} (hP : P.Simple) (hL : P.InteriorLeft)
  (hC : CorridorAt P I a b) {k : ℕ} (hk : k < I.np)
include hg hP hL hC hk

/-- **The stationary guard of pair `k` is pinned by its two slot tips**: every point of the plane
seeing both tips `q_a = slotTip k 2` and `q_b = slotTip k 4` is `p_k`. -/
theorem Good.sg_unique {x : Point} (hxa : P.Sees x (ratPoint (I.slotTip k 2)))
    (hxb : P.Sees x (ratPoint (I.slotTip k 4))) : x = ratPoint (I.sgPt k) := by
  have hn : 0 < P.n := by have := hP.1; omega
  obtain ⟨A₁, A₂, hA⟩ := chainAfter_infix_sg hk
  obtain ⟨B₁, B₂, hB⟩ := chainBefore_infix_slot2 hk
  obtain ⟨C₁, C₂, hCc⟩ := chainBefore_infix_slot4 hk
  obtain ⟨hp₁, -, hw, hu, hp₀⟩ := vtx_triple hn hC.after hA
  obtain ⟨hqa, hua, hwa, -, -⟩ := vtx_triple (x := (I.kx k 2 - I.ε / 8, I.H))
    (y := I.slotTip k 2) (z := (I.kx k 2, I.H)) hn hC.before (by rw [hB]; rfl)
  obtain ⟨hqb, hub, hwb, -, -⟩ := vtx_triple (x := (I.kx k 4, I.H))
    (y := I.slotTip k 4) (z := (I.kx k 4 + I.ε / 8, I.H)) hn hC.before (by rw [hCc]; rfl)
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15⟩ :=
    (hg.sgConfig hk).dets' (p := I.sgPt k) (u := I.base k) (w := I.zp k)
      (qa := I.slotTip k 2) (ua := (I.kx k 2 - I.ε / 8, I.H)) (wa := (I.kx k 2, I.H))
      (qb := I.slotTip k 4) (ub := (I.kx k 4, I.H)) (wb := (I.kx k 4 + I.ε / 8, I.H)) rfl
      (Prod.ext rfl rfl) (Prod.ext rfl (hg.zp_on_axis hk)) rfl rfl rfl rfl rfl rfl
  have c : ∀ x y z : ℚ × ℚ, det (ratPoint x) (ratPoint y) (ratPoint z) = ((det2 x y z : ℚ) : ℝ) :=
    det_ratPoint
  exact Polygon.sg_unique_of_vertices hP hL (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)
    (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) hu hp₀ hp₁ hw hua hqa hwa
    (by rw [c]; exact_mod_cast d1) hub hqb hwb (by rw [c]; exact_mod_cast d2)
    (by rw [c]; exact_mod_cast d3) (by rw [c]; exact_mod_cast d4) (by rw [c]; exact_mod_cast d5)
    (by rw [c]; exact_mod_cast d6) (by rw [c]; exact_mod_cast d7) (by rw [c]; exact_mod_cast d8)
    (by rw [c]; exact_mod_cast d9) (by rw [c]; exact_mod_cast d10)
    (by rw [c]; exact_mod_cast d11) (by rw [c]; exact_mod_cast d12)
    (by rw [c]; exact_mod_cast d13) (by rw [c]; exact_mod_cast d14)
    (by rw [c]; exact_mod_cast d15) hxa hxb

end SG

end Input

end ArtGallery.Sec5.Corridor

end
