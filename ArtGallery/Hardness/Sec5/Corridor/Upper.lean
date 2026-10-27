module

public import ArtGallery.Hardness.Sec5.Corridor.Floor

/-!
# Section 5: corridors — the upper wall is monotone

The upper wall `d1, [valley_k], p_k, z'_k, z1, n1, n0, z0, …, d0` (westward) is `x`-monotone:
every edge goes strictly west except the vertical edges `d1 → p_0`, `valley_k → p_k`,
`z1 → n1`, `n0 → z0`, and no two vertical edges are consecutive (`xMono_chainAfter`).  Hence it is
a simple polyline (`chainSimple_chainAfter`).

**Vertex facts** (`Good.feature_*`): every vertex except `d1`, `p_0`, `d0` lies in the window
`|lX|, |lY| ≤ 456N` (so strictly between the lines `x = S`, `x = S + 2` and strictly above
`y = H + ρ`).

The list of the upper wall is written out for `p = 1, 2, 3` pairs (`chainAfter_one`, …).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set

/-- `x`-monotone chains over `ℚ` (the `ℚ` version of `XMono`). -/
def XMonoQ : List (ℚ × ℚ) → Prop
  | a :: b :: l => (b.1 < a.1 ∨ (b.1 = a.1 ∧ b.2 ≠ a.2 ∧ ∀ c ∈ l.head?, c.1 < b.1)) ∧
      XMonoQ (b :: l)
  | _ => True

theorem xMonoQ_cons_cons {a b : ℚ × ℚ} {l : List (ℚ × ℚ)} :
    XMonoQ (a :: b :: l) ↔ (b.1 < a.1 ∨ (b.1 = a.1 ∧ b.2 ≠ a.2 ∧ ∀ c ∈ l.head?, c.1 < b.1)) ∧
      XMonoQ (b :: l) := Iff.rfl

/-- Monotone chains over `ℚ` stay monotone over `ℝ`. -/
theorem XMonoQ.map {L : List (ℚ × ℚ)} (h : XMonoQ L) : XMono (L.map ratPoint) := by
  induction L with
  | nil => trivial
  | cons a L ih =>
    cases L with
    | nil => trivial
    | cons b l =>
      refine ⟨?_, ih h.2⟩
      simp only [ratPoint_fst, ratPoint_snd]
      rcases h.1 with h1 | ⟨h1, h2, h3⟩
      · left; exact_mod_cast h1
      · right
        refine ⟨by exact_mod_cast h1, fun h' => h2 (by exact_mod_cast h'), ?_⟩
        intro c hc
        cases l with
        | nil => simp at hc
        | cons c' l =>
          simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hc
          subst hc
          simp only [ratPoint_fst]
          exact_mod_cast h3 c' (by simp)

namespace Input

variable {I : Input} {N : ℚ}

/-! ## The upper wall as an explicit list -/

theorem upper_one (h : I.np = 1) : I.upper = I.upperPair 0 := by
  simp [upper, h]

theorem upper_two (h : I.np = 2) : I.upper = I.upperPair 0 ++ I.upperPair 1 := by
  simp [upper, h, List.range_succ]

theorem upper_three (h : I.np = 3) :
    I.upper = I.upperPair 0 ++ I.upperPair 1 ++ I.upperPair 2 := by
  simp [upper, h, List.range_succ]

theorem upperPair_zero :
    I.upperPair 0 = [I.sgPt 0, I.zp 0, I.z1 0, I.n1 0, I.n0 0, I.z0 0] := by
  simp [upperPair]

theorem upperPair_succ (k : ℕ) :
    I.upperPair (k + 1) = [I.valley (k + 1), I.sgPt (k + 1), I.zp (k + 1), I.z1 (k + 1),
      I.n1 (k + 1), I.n0 (k + 1), I.z0 (k + 1)] := by
  simp [upperPair]

/-! ## Comparisons in local coordinates -/

theorem fst_lt_iff (hg : I.Good N) {a b : ℚ × ℚ} : a.1 < b.1 ↔ I.lX a < I.lX b := by
  have := hg.S_pos
  simp only [lX_def]
  constructor
  · intro h; nlinarith
  · intro h; by_contra h'; push Not at h'; nlinarith

theorem fst_eq_iff (hg : I.Good N) {a b : ℚ × ℚ} : a.1 = b.1 ↔ I.lX a = I.lX b := by
  have := hg.S_pos
  simp only [lX_def]
  constructor
  · intro h; rw [h]
  · intro h
    have : 8 * I.S * (a.1 - b.1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · linarith

theorem snd_ne_iff (hg : I.Good N) {a b : ℚ × ℚ} : a.2 ≠ b.2 ↔ I.lY a ≠ I.lY b := by
  have := hg.S_pos
  simp only [lY_def, ne_eq]
  constructor
  · intro h h'; apply h
    have : 8 * I.S * (a.2 - b.2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · linarith
  · intro h h'; apply h; rw [h']

theorem snd_lt_iff (hg : I.Good N) {a b : ℚ × ℚ} : a.2 < b.2 ↔ I.lY a < I.lY b := by
  have := hg.S_pos
  simp only [lY_def]
  constructor
  · intro h; nlinarith
  · intro h; by_contra h'; push Not at h'; nlinarith

/-! ## Vertex facts -/

/-- A vertex in the window around the features. -/
def InWindow (I : Input) (N : ℚ) (z : ℚ × ℚ) : Prop := |I.lX z| ≤ 456 * N ∧ |I.lY z| ≤ 456 * N

theorem abs_sub_le_one_of {x a c : ℚ} (h : |x - a| ≤ 1 / 8) (hc : a = c) : |x - c| ≤ 1 := by
  rw [← hc]; linarith

section Features

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

theorem Good.ab_bound : |(I.lwE k + I.rwE k) / 2| ≤ 68 * N + 410 := by
  have := hg.lwE_bound hk; have := hg.rwE_bound hk; have := hg.N_ge
  rw [abs_le]; constructor <;> linarith

theorem Good.feature_lY {z : ℚ × ℚ} {c : ℚ} (hc : |c| ≤ 20)
    (hz : |I.lY z - ((I.lwE k + I.rwE k) / 2 + c)| ≤ 1) : |I.lY z| ≤ 456 * N := by
  have h1 := hg.ab_bound hk; have := hg.N_ge
  rw [abs_le] at hz hc h1 ⊢
  constructor <;> linarith


theorem Good.feature_zp : InWindow I N (I.zp k) :=
  ⟨hg.lX_zp_window hk, hg.feature_lY hk (c := -16) (by norm_num)
    (abs_sub_le_one_of (hg.lY_zp hk) (by ring))⟩

theorem Good.feature_z1 : InWindow I N (I.z1 k) := by
  have := hg.window_apex hk
  refine ⟨?_, hg.feature_lY hk (c := -3) (by norm_num) (by rw [lY_z1 hg hk]; ring_nf; norm_num)⟩
  rw [lX_z1 hg hk]
  rw [abs_le]; constructor <;>
    rcases abs_cases ((I.rwE k - I.lwE k) / 2) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith

theorem Good.feature_z0 : InWindow I N (I.z0 k) := by
  have := hg.window_apex hk
  refine ⟨?_, hg.feature_lY hk (c := -3) (by norm_num) (by rw [lY_z0 hg hk]; ring_nf; norm_num)⟩
  rw [lX_z0 hg hk]
  rw [abs_le]; constructor <;>
    rcases abs_cases ((I.rwE k - I.lwE k) / 2) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith

theorem Good.feature_n1 : InWindow I N (I.n1 k) :=
  ⟨by rw [lX_n1]; exact (hg.feature_z1 hk).1,
    hg.feature_lY hk (c := -1) (by norm_num) (abs_sub_le_one_of (hg.lY_n1 hk) (by ring))⟩

theorem Good.feature_n0 : InWindow I N (I.n0 k) :=
  ⟨by rw [lX_n0]; exact (hg.feature_z0 hk).1,
    hg.feature_lY hk (c := 1) (by norm_num) (abs_sub_le_one_of (hg.lY_n0 hk) (by ring))⟩

variable (hk1 : 1 ≤ k)
include hk1

theorem Good.feature_sgPt : InWindow I N (I.sgPt k) := by
  have := hg.window_valley hk hk1
  refine ⟨?_, hg.feature_lY hk (c := -16) (by norm_num)
    (abs_sub_le_one_of (hg.lY_sgPt hk hk1) (by ring))⟩
  rw [lX_sgPt hg hk hk1]; linarith [abs_nonneg ((I.rwE k - I.lwE (k - 1)) / 2 + 1 / 4)]

theorem Good.feature_valley : InWindow I N (I.valley k) := by
  have := hg.window_valley hk hk1
  refine ⟨?_, ?_⟩
  · rw [lX_valley hg hk]; linarith [abs_nonneg ((I.rwE k - I.lwE (k - 1)) / 2 + 1 / 4)]
  · rw [lY_valley hg hk]
    have := hg.lwE_bound (k := k - 1) (by omega); have := hg.rwE_bound hk; have := hg.N_ge
    rw [abs_le]; constructor <;> linarith

end Features

/-! ## Monotonicity of the upper wall -/

section Mono

variable (hg : I.Good N)
include hg

/-- The edges of pair `k` from `z'_k` to `z0` (the inner part). -/
theorem Good.xMonoQ_inner {k : ℕ} (hk : k < I.np) (l : List (ℚ × ℚ))
    (hl : ∀ c ∈ l.head?, c.1 < (I.z0 k).1) (hrest : XMonoQ (I.z0 k :: l)) :
    XMonoQ (I.zp k :: I.z1 k :: I.n1 k :: I.n0 k :: I.z0 k :: l) := by
  have hzp := hg.lX_zp hk
  have hn1 := hg.lY_n1 hk
  have hn0 := hg.lY_n0 hk
  rw [abs_le] at hzp hn1 hn0
  refine ⟨Or.inl ?_, Or.inr ⟨?_, ?_, ?_⟩, Or.inl ?_, Or.inr ⟨?_, ?_, hl⟩, hrest⟩
  · rw [fst_lt_iff hg, lX_z1 hg hk]; linarith
  · rfl
  · rw [snd_ne_iff hg, lY_z1 hg hk]; intro h; linarith
  · intro c hc
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc
    subst hc
    rw [fst_lt_iff hg, lX_n0, lX_n1, lX_z1 hg hk, lX_z0 hg hk]; linarith
  · rw [fst_lt_iff hg, lX_n0, lX_n1, lX_z1 hg hk, lX_z0 hg hk]; linarith
  · rfl
  · rw [snd_ne_iff hg, lY_z0 hg hk]; intro h; linarith

/-- `p_k → z'_k` goes strictly west. -/
theorem Good.zp_lt_sgPt {k : ℕ} (hk : k < I.np) : (I.zp k).1 < (I.sgPt k).1 := by
  rw [fst_lt_iff hg]
  have hzp := hg.lX_zp hk
  rw [abs_le] at hzp
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · rw [lX_sgPt_zero]
    have := hg.window_apex hk; have := hg.scale.S_ge; have := hg.N_ge; have := hg.S_eq
    have := abs_nonneg ((I.rwE 0 - I.lwE 0) / 2)
    rcases abs_cases ((I.rwE 0 - I.lwE 0) / 2) with ⟨h, _⟩ | ⟨h, _⟩ <;> nlinarith
  · rw [lX_sgPt hg hk hk1]
    have := hg.lwE_succ (k := k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at this
    linarith

/-- `z0_k → valley_{k+1}` goes strictly west. -/
theorem Good.valley_lt_z0 {k : ℕ} (hk : k + 1 < I.np) : (I.valley (k + 1)).1 < (I.z0 k).1 := by
  rw [fst_lt_iff hg, lX_valley hg hk, lX_z0 hg (by omega), hg.rwE_succ hk]
  simp only [Nat.add_sub_cancel]
  linarith

/-- `valley_k → p_k` is vertical and nondegenerate. -/
theorem Good.sgPt_valley {k : ℕ} (hk : k < I.np) (hk1 : 1 ≤ k) :
    (I.sgPt k).1 = (I.valley k).1 ∧ (I.sgPt k).2 ≠ (I.valley k).2 := by
  refine ⟨?_, ?_⟩
  · show (I.base k).1 = _; simp [base, show k ≠ 0 by omega]
  · rw [snd_ne_iff hg, lY_valley hg hk]
    have h1 := hg.lY_sgPt hk hk1
    have h2 := hg.lwE_succ (k := k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at h2
    rw [abs_le] at h1
    intro h; linarith

/-- `d1 → p_0` is vertical and nondegenerate. -/
theorem Good.sgPt_d1 (h0 : 0 < I.np) :
    (I.sgPt 0).1 = (d1 I.S I.H).1 ∧ (I.sgPt 0).2 ≠ (d1 I.S I.H).2 := by
  refine ⟨by simp [sgPt, base_zero, onUmbra], ?_⟩
  rw [snd_ne_iff hg, lY_d1 hg]
  have hb := hg.lY_sgPt_zero_abs h0
  have := hg.scale.S_ge; have := hg.N_ge; have := hg.S_eq
  rw [abs_le] at hb
  intro h; nlinarith

/-- The last edge `z0 → d0` goes strictly west. -/
theorem Good.d0_lt_z0 {k : ℕ} (hk : k < I.np) : (d0 I.S I.H).1 < (I.z0 k).1 := by
  rw [fst_lt_iff hg, lX_d0, lX_z0 hg hk]
  have := hg.window_apex hk; have := hg.scale.S_ge; have := hg.N_ge; have := hg.S_eq
  rcases abs_cases ((I.rwE k - I.lwE k) / 2) with ⟨h, _⟩ | ⟨h, _⟩ <;> nlinarith

/-- The pieces `valley_k, p_k, …` of later pairs. -/
theorem Good.xMonoQ_later {k : ℕ} (hk : k < I.np) (hk1 : 1 ≤ k) (l : List (ℚ × ℚ))
    (hl : ∀ c ∈ l.head?, c.1 < (I.z0 k).1) (hrest : XMonoQ (I.z0 k :: l)) :
    XMonoQ (I.valley k :: I.sgPt k :: I.zp k :: I.z1 k :: I.n1 k :: I.n0 k :: I.z0 k :: l) := by
  obtain ⟨h1, h2⟩ := hg.sgPt_valley hk hk1
  refine ⟨Or.inr ⟨h1, h2, ?_⟩, Or.inl (hg.zp_lt_sgPt hk), hg.xMonoQ_inner hk l hl hrest⟩
  intro c hc
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc
  subst hc
  exact hg.zp_lt_sgPt hk

/-- **The upper wall is `x`-monotone.** -/
theorem Good.xMonoQ_chainAfter : XMonoQ I.chainAfter := by
  have hp := hg.np_pos
  have hp3 := hg.np_le
  have h0 : 0 < I.np := by omega
  obtain ⟨h1, h2⟩ := hg.sgPt_d1 h0
  -- the head `d1, p_0`
  have head : ∀ l, XMonoQ (I.zp 0 :: l) →
      XMonoQ (d1 I.S I.H :: I.sgPt 0 :: I.zp 0 :: l) := fun l hl =>
    ⟨Or.inr ⟨h1, h2, fun c hc => by
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc
      subst hc; exact hg.zp_lt_sgPt h0⟩, Or.inl (hg.zp_lt_sgPt h0), hl⟩
  have tail : ∀ k < I.np, XMonoQ [I.z0 k, d0 I.S I.H] := fun k hk =>
    ⟨Or.inl (hg.d0_lt_z0 hk), trivial⟩
  rcases (by omega : I.np = 1 ∨ I.np = 2 ∨ I.np = 3) with hnp | hnp | hnp
  · -- one pair
    rw [chainAfter, upper_one hnp, upperPair_zero]
    simp only [List.cons_append, List.nil_append]
    exact head _ (hg.xMonoQ_inner h0 _ (by simp; exact hg.d0_lt_z0 h0) (tail 0 h0))
  · -- two pairs
    rw [chainAfter, upper_two hnp, upperPair_zero, upperPair_succ]
    simp only [List.cons_append, List.nil_append, zero_add]
    refine head _ (hg.xMonoQ_inner h0 _ (by simp; exact hg.valley_lt_z0 (k := 0) (by omega))
      ⟨Or.inl (hg.valley_lt_z0 (k := 0) (by omega)), ?_⟩)
    exact hg.xMonoQ_later (k := 1) (by omega) le_rfl _ (by simp; exact hg.d0_lt_z0 (by omega))
      (tail 1 (by omega))
  · -- three pairs
    rw [chainAfter, upper_three hnp, upperPair_zero, upperPair_succ, upperPair_succ]
    simp only [List.cons_append, List.nil_append, zero_add]
    refine head _ (hg.xMonoQ_inner h0 _ (by simp; exact hg.valley_lt_z0 (k := 0) (by omega))
      ⟨Or.inl (hg.valley_lt_z0 (k := 0) (by omega)), ?_⟩)
    refine hg.xMonoQ_later (k := 1) (by omega) le_rfl _
      (by simp; exact hg.valley_lt_z0 (k := 1) (by omega))
      ⟨Or.inl (hg.valley_lt_z0 (k := 1) (by omega)), ?_⟩
    exact hg.xMonoQ_later (k := 2) (by omega) (by norm_num) _
      (by simp; exact hg.d0_lt_z0 (by omega)) (tail 2 (by omega))

/-- **The upper wall is a simple polyline.** -/
theorem Good.chainSimple_chainAfter : ChainSimple (I.chainAfter.map ratPoint) :=
  chainSimple_of_xMono hg.xMonoQ_chainAfter.map

end Mono

end Input

end ArtGallery.Sec5.Corridor

end
