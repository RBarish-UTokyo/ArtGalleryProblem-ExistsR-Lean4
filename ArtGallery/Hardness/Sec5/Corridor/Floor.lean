module

public import ArtGallery.Hardness.Sec5.Corridor.Bounds
public import ArtGallery.Hardness.Sec5.Corridor.Chain

/-!
# Section 5: corridors — the floor

The corridor floor `c0, slots…, c1` lies on the line `y = H`, interrupted by the witness slots of
the stationary guards (thin triangles below the line).

* **Slot keys** (`Good.kx_*`): the slots of the first pair lie at `x ≈ S + 3/2` (slope 2) and
  `x ≈ S + 7/4` (slope 4), those of the later pairs at `x ≈ S + 1/2` and `x ≈ S + 3/4`, all within
  `1/1000`; within a group the keys decrease from pair to pair by at least `100ε`.
* **Sorted order** (`floor_eq_one`, `floor_eq_two`, `floor_eq_three`): the floor is
  `slot2 (p−1), …, slot2 1, slot4 (p−1), …, slot4 1, slot2 0, slot4 0`.
* **Dents** (`dent2`, `dent4`): a slope-2 slot lies in the slanted strip
  `x − (y − H)/2 ∈ [κ − ε/8, κ]`, a slope-4 slot in `x − (y − H)/4 ∈ [κ, κ + ε/8]`
  (`κ` = key), both of depth `≤ 1/4`.
* **The floor chain is simple** (`chainSimple_chainBefore`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set

/-! ## Sorting with distinct keys -/

/-- Two permutations of each other, the first weakly and the second strictly sorted by a key, are
equal. -/
theorem eq_of_perm_of_pairwise {α : Type*} (key : α → ℚ) :
    ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.Pairwise (fun a b => key a ≤ key b) →
      l₂.Pairwise (fun a b => key a < key b) → l₁ = l₂
  | [], l₂, hp, _, _ => List.Perm.nil_eq hp
  | b :: t₁, [], hp, _, _ => absurd (List.Perm.length_eq hp) (by simp)
  | b :: t₁, a :: t₂, hp, h₁, h₂ => by
    have hab : a = b := by
      by_contra hne
      have hb : b ∈ t₂ := by
        have : b ∈ a :: t₂ := hp.subset (List.mem_cons_self)
        rcases List.mem_cons.1 this with h | h
        · exact absurd h.symm hne
        · exact h
      have ha : a ∈ t₁ := by
        have : a ∈ b :: t₁ := hp.symm.subset (List.mem_cons_self)
        rcases List.mem_cons.1 this with h | h
        · exact absurd h hne
        · exact h
      have h1 := (List.pairwise_cons.1 h₂).1 b hb
      have h2 := (List.pairwise_cons.1 h₁).1 a ha
      linarith
    subst hab
    rw [eq_of_perm_of_pairwise key ((List.perm_cons a).1 hp) (List.pairwise_cons.1 h₁).2
      (List.pairwise_cons.1 h₂).2]

/-- `mergeSort` by a key is the unique strictly sorted permutation. -/
theorem mergeSort_eq_of_perm {α : Type*} (key : α → ℚ) {l l' : List α} (hp : l'.Perm l)
    (hs : l'.Pairwise (fun a b => key a < key b)) :
    l.mergeSort (fun a b => decide (key a ≤ key b)) = l' := by
  apply eq_of_perm_of_pairwise key ((List.mergeSort_perm _ _).trans hp.symm) _ hs
  have := List.pairwise_mergeSort (le := fun a b => decide (key a ≤ key b))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at h1 h2 ⊢; linarith)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _) l
  simpa using this

/-! ## Dents of slope 2 and 4 -/

section Dents

variable (κ H e : ℝ)

/-- The slanted strip containing a slope-2 slot with key `κ`. -/
def R2 : Set Point :=
  {z | H - 1 / 8 ≤ z.2 ∧ z.2 ≤ H ∧ κ - e / 8 ≤ z.1 - (z.2 - H) / 2 ∧ z.1 - (z.2 - H) / 2 ≤ κ}

/-- The slanted strip containing a slope-4 slot with key `κ`. -/
def R4 : Set Point :=
  {z | H - 1 / 4 ≤ z.2 ∧ z.2 ≤ H ∧ κ ≤ z.1 - (z.2 - H) / 4 ∧ z.1 - (z.2 - H) / 4 ≤ κ + e / 8}

/-- The slope-2 slot `(κ − e/8, H), (κ − 1/16, H − 1/8), (κ, H)` as a dent. -/
noncomputable def dent2 : Dent := ⟨(κ - e / 8, H), (κ - 1 / 16, H - 1 / 8), (κ, H), R2 κ H e⟩

/-- The slope-4 slot `(κ, H), (κ − 1/16, H − 1/4), (κ + e/8, H)` as a dent. -/
noncomputable def dent4 : Dent := ⟨(κ, H), (κ - 1 / 16, H - 1 / 4), (κ + e / 8, H), R4 κ H e⟩

variable {κ H e}

/-- An affine inequality valid at both endpoints holds on the segment. -/
theorem seg_affine_le {p q z : Point} (hz : z ∈ ArtGallery.segment p q) {α β c : ℝ}
    (hp : α * p.1 + β * p.2 ≤ c) (hq : α * q.1 + β * q.2 ≤ c) : α * z.1 + β * z.2 ≤ c := by
  obtain ⟨t, h0, h1, hx, hy⟩ := Irrational.mem_segment_coords hz
  rw [hx, hy]
  nlinarith [mul_nonneg h0 (sub_nonneg.2 hq), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hp)]

theorem R2_seg {p q : Point} (hp : p ∈ R2 κ H e) (hq : q ∈ R2 κ H e) :
    ArtGallery.segment p q ⊆ R2 κ H e := by
  intro z hz
  obtain ⟨p1, p2, p3, p4⟩ := hp
  obtain ⟨q1, q2, q3, q4⟩ := hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := seg_affine_le hz (α := 0) (β := -1) (c := -(H - 1 / 8)) (by linarith) (by linarith)
    linarith
  · have := seg_affine_le hz (α := 0) (β := 1) (c := H) (by linarith) (by linarith)
    linarith
  · have := seg_affine_le hz (α := -1) (β := 1 / 2) (c := -(κ - e / 8) + H / 2)
      (by linarith) (by linarith)
    linarith
  · have := seg_affine_le hz (α := 1) (β := -1 / 2) (c := κ - H / 2) (by linarith) (by linarith)
    linarith

theorem R4_seg {p q : Point} (hp : p ∈ R4 κ H e) (hq : q ∈ R4 κ H e) :
    ArtGallery.segment p q ⊆ R4 κ H e := by
  intro z hz
  obtain ⟨p1, p2, p3, p4⟩ := hp
  obtain ⟨q1, q2, q3, q4⟩ := hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := seg_affine_le hz (α := 0) (β := -1) (c := -(H - 1 / 4)) (by linarith) (by linarith)
    linarith
  · have := seg_affine_le hz (α := 0) (β := 1) (c := H) (by linarith) (by linarith)
    linarith
  · have := seg_affine_le hz (α := -1) (β := 1 / 4) (c := -κ + H / 4) (by linarith) (by linarith)
    linarith
  · have := seg_affine_le hz (α := 1) (β := -1 / 4) (c := κ + e / 8 - H / 4) (by linarith)
      (by linarith)
    linarith

theorem dent2_ok (he : 0 < e) (he1 : e < 1) : (dent2 κ H e).OK H := by
  have hA : ((κ - e / 8, H) : Point) ∈ R2 κ H e := ⟨by linarith, le_rfl, by simp, by simp; linarith⟩
  have hT : ((κ - 1 / 16, H - 1 / 8) : Point) ∈ R2 κ H e :=
    ⟨le_rfl, by linarith, by simp only; linarith, by simp only; linarith⟩
  have hB : ((κ, H) : Point) ∈ R2 κ H e := ⟨by linarith, le_rfl, by simp; linarith, by simp⟩
  refine ⟨rfl, rfl, by simp only [dent2]; linarith, by simp only [dent2]; linarith,
    R2_seg hA hT, R2_seg hT hB, fun z hz => hz.2.1, fun z hz hzy => ?_, ?_⟩
  · obtain ⟨-, -, h3, h4⟩ := hz
    simp only [dent2]
    rw [hzy] at h3 h4
    constructor <;> linarith
  · intro z hz
    rw [mem_singleton_iff]
    refine Irrational.eq_of_mem_segment_adjacent ?_ hz.1 hz.2
    simp only [dent2, det]
    nlinarith

theorem dent4_ok (he : 0 < e) (he1 : e < 1) : (dent4 κ H e).OK H := by
  have hA : ((κ, H) : Point) ∈ R4 κ H e := ⟨by linarith, le_rfl, by simp, by simp; linarith⟩
  have hT : ((κ - 1 / 16, H - 1 / 4) : Point) ∈ R4 κ H e :=
    ⟨le_rfl, by linarith, by simp only; linarith, by simp only; linarith⟩
  have hB : ((κ + e / 8, H) : Point) ∈ R4 κ H e := ⟨by linarith, le_rfl, by simp; linarith, by simp⟩
  refine ⟨rfl, rfl, by simp only [dent4]; linarith, by simp only [dent4]; linarith,
    R4_seg hA hT, R4_seg hT hB, fun z hz => hz.2.1, fun z hz hzy => ?_, ?_⟩
  · obtain ⟨-, -, h3, h4⟩ := hz
    simp only [dent4]
    rw [hzy] at h3 h4
    constructor <;> linarith
  · intro z hz
    rw [mem_singleton_iff]
    refine Irrational.eq_of_mem_segment_adjacent ?_ hz.1 hz.2
    simp only [dent4, det]
    nlinarith

/-- Abscissae of a slope-2 strip. -/
theorem R2_fst {z : Point} (hz : z ∈ R2 κ H e) : κ - e / 8 - 1 / 16 ≤ z.1 ∧ z.1 ≤ κ := by
  obtain ⟨h1, h2, h3, h4⟩ := hz; constructor <;> linarith

/-- Abscissae of a slope-4 strip. -/
theorem R4_fst {z : Point} (hz : z ∈ R4 κ H e) : κ - 1 / 16 ≤ z.1 ∧ z.1 ≤ κ + e / 8 := by
  obtain ⟨h1, h2, h3, h4⟩ := hz; constructor <;> linarith

theorem disjoint_R2_R2 {κ' : ℝ} (h : κ < κ' - e / 8) : Disjoint (R2 κ H e) (R2 κ' H e) := by
  rw [Set.disjoint_left]
  rintro z ⟨-, -, -, h1⟩ ⟨-, -, h2, -⟩
  linarith

theorem disjoint_R4_R4 {κ' : ℝ} (h : κ + e / 8 < κ') : Disjoint (R4 κ H e) (R4 κ' H e) := by
  rw [Set.disjoint_left]
  rintro z ⟨-, -, -, h1⟩ ⟨-, -, h2, -⟩
  linarith

/-- Strips with disjoint abscissa ranges are disjoint. -/
theorem disjoint_of_fst {A B : Set Point} {a b : ℝ} (hA : ∀ z ∈ A, z.1 ≤ a)
    (hB : ∀ z ∈ B, b ≤ z.1) (hab : a < b) : Disjoint A B := by
  rw [Set.disjoint_left]
  intro z hzA hzB
  linarith [hA z hzA, hB z hzB]

end Dents

namespace Input

variable {I : Input} {N : ℚ}

/-! ## Slot keys -/

/-- The slot key in local `ε`-units: `8S (kx − O.x) = lX(p) − (8S + lY(p))/s`. -/
theorem kx_local (hg : I.Good N) (k : ℕ) {s : ℚ} (hs : s ≠ 0) :
    8 * I.S * (I.kx k s - (I.S + 1)) = I.lX (I.sgPt k) - (8 * I.S + I.lY (I.sgPt k)) / s := by
  have hS := hg.S_pos
  simp only [kx, lX_def, lY_def]
  field_simp
  ring

section Keys

variable (hg : I.Good N)
include hg

theorem Good.kx_zero_two (h0 : 0 < I.np) : |I.kx 0 2 - (I.S + 3 / 2)| ≤ 1 / 1000 := by
  have hS := hg.S_pos
  have hl := kx_local hg 0 (s := 2) (by norm_num)
  rw [lX_sgPt_zero] at hl
  have hb := hg.lY_sgPt_zero_abs h0
  have hN := hg.N_ge
  have hS' := hg.S_eq
  have e : I.kx 0 2 - (I.S + 3 / 2) = -I.lY (I.sgPt 0) / (16 * I.S) := by
    rw [eq_div_iff (by positivity)]; linear_combination 2 * hl
  rw [e]
  apply abs_div_le_of (by positivity)
  rw [abs_neg]
  nlinarith

theorem Good.kx_zero_four (h0 : 0 < I.np) : |I.kx 0 4 - (I.S + 7 / 4)| ≤ 1 / 1000 := by
  have hS := hg.S_pos
  have hl := kx_local hg 0 (s := 4) (by norm_num)
  rw [lX_sgPt_zero] at hl
  have hb := hg.lY_sgPt_zero_abs h0
  have hN := hg.N_ge
  have hS' := hg.S_eq
  have e : I.kx 0 4 - (I.S + 7 / 4) = -I.lY (I.sgPt 0) / (32 * I.S) := by
    rw [eq_div_iff (by positivity)]; linear_combination 4 * hl
  rw [e]
  apply abs_div_le_of (by positivity)
  rw [abs_neg]
  nlinarith

variable {k : ℕ} (hk : k < I.np) (hk1 : 1 ≤ k)
include hk hk1

/-- Height of a later stationary guard in absolute terms. -/
theorem Good.lY_sgPt_abs : |I.lY (I.sgPt k)| ≤ 68 * N + 400 := by
  have h1 := hg.lY_sgPt hk hk1
  have h2 := hg.lwE_bound hk
  have h3 := hg.rwE_bound hk
  rw [abs_le] at h1 ⊢
  constructor <;> linarith

theorem Good.kx_two : |I.kx k 2 - (I.S + 1 / 2)| ≤ 1 / 1000 := by
  have hS := hg.S_pos
  have hl := kx_local hg k (s := 2) (by norm_num)
  have hb := hg.lY_sgPt_abs hk hk1
  have hx := hg.window_valley hk hk1
  rw [← lX_sgPt hg hk hk1] at hx
  have hN := hg.N_ge
  have hS' := hg.S_eq
  have e : I.kx k 2 - (I.S + 1 / 2) = (I.lX (I.sgPt k) - I.lY (I.sgPt k) / 2) / (8 * I.S) := by
    rw [eq_div_iff (by positivity)]; linear_combination hl
  rw [e]
  apply abs_div_le_of (by positivity)
  have : |I.lX (I.sgPt k) - I.lY (I.sgPt k) / 2| ≤ 456 * N + (68 * N + 400) := by
    rw [abs_le] at hb ⊢
    have := abs_nonneg (I.lX (I.sgPt k))
    rcases abs_cases (I.lX (I.sgPt k)) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hx <;>
      constructor <;> linarith
  nlinarith

theorem Good.kx_four : |I.kx k 4 - (I.S + 3 / 4)| ≤ 1 / 1000 := by
  have hS := hg.S_pos
  have hl := kx_local hg k (s := 4) (by norm_num)
  have hb := hg.lY_sgPt_abs hk hk1
  have hx := hg.window_valley hk hk1
  rw [← lX_sgPt hg hk hk1] at hx
  have hN := hg.N_ge
  have hS' := hg.S_eq
  have e : I.kx k 4 - (I.S + 3 / 4) = (I.lX (I.sgPt k) - I.lY (I.sgPt k) / 4) / (8 * I.S) := by
    rw [eq_div_iff (by positivity)]; linear_combination hl
  rw [e]
  apply abs_div_le_of (by positivity)
  have : |I.lX (I.sgPt k) - I.lY (I.sgPt k) / 4| ≤ 456 * N + (68 * N + 400) := by
    rw [abs_le] at hb ⊢
    have := abs_nonneg (I.lX (I.sgPt k))
    rcases abs_cases (I.lX (I.sgPt k)) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hx <;>
      constructor <;> linarith
  nlinarith

omit hk in
/-- Within the group of later pairs, the slope-2 keys decrease by at least `100ε`. -/
theorem Good.kx_two_succ (hk' : k + 1 < I.np) : I.kx (k + 1) 2 + 100 * I.ε ≤ I.kx k 2 := by
  have hk : k < I.np := by omega
  have hS := hg.S_pos
  have h1 := kx_local hg k (s := 2) (by norm_num)
  have h2 := kx_local hg (k + 1) (s := 2) (by norm_num)
  have e1 := lX_sgPt hg hk hk1
  have e2 := lX_sgPt hg hk' (by omega)
  have y1 := hg.lY_sgPt hk hk1
  have y2 := hg.lY_sgPt hk' (by omega)
  have hr := hg.rwE_succ hk'
  have hl1 := hg.lwE_succ hk'
  have hl0 := hg.lwE_succ (k := k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at hl0
  rw [show k + 1 - 1 = k by omega] at e2
  rw [abs_le] at y1 y2
  have key : 8 * I.S * (I.kx (k + 1) 2 - (I.S + 1)) + 100 ≤ 8 * I.S * (I.kx k 2 - (I.S + 1)) := by
    rw [h1, h2, e1, e2]; linarith
  rw [Input.ε, eps]
  have : 100 * (1 / (8 * I.S)) = 100 / (8 * I.S) := by ring
  rw [this, ← sub_nonneg]
  have h8 : 0 < 8 * I.S := by positivity
  have : I.kx k 2 - (I.kx (k + 1) 2 + 100 / (8 * I.S)) =
      ((8 * I.S * (I.kx k 2 - (I.S + 1))) - (8 * I.S * (I.kx (k + 1) 2 - (I.S + 1))) - 100) /
        (8 * I.S) := by field_simp; ring
  rw [this]
  apply div_nonneg _ h8.le
  linarith

omit hk in
/-- Within the group of later pairs, the slope-4 keys decrease by at least `100ε`. -/
theorem Good.kx_four_succ (hk' : k + 1 < I.np) : I.kx (k + 1) 4 + 100 * I.ε ≤ I.kx k 4 := by
  have hk : k < I.np := by omega
  have hS := hg.S_pos
  have h1 := kx_local hg k (s := 4) (by norm_num)
  have h2 := kx_local hg (k + 1) (s := 4) (by norm_num)
  have e1 := lX_sgPt hg hk hk1
  have e2 := lX_sgPt hg hk' (by omega)
  have y1 := hg.lY_sgPt hk hk1
  have y2 := hg.lY_sgPt hk' (by omega)
  have hr := hg.rwE_succ hk'
  have hl1 := hg.lwE_succ hk'
  have hl0 := hg.lwE_succ (k := k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at hl0
  rw [show k + 1 - 1 = k by omega] at e2
  rw [abs_le] at y1 y2
  have key : 8 * I.S * (I.kx (k + 1) 4 - (I.S + 1)) + 100 ≤ 8 * I.S * (I.kx k 4 - (I.S + 1)) := by
    rw [h1, h2, e1, e2]; linarith
  rw [Input.ε, eps]
  have : 100 * (1 / (8 * I.S)) = 100 / (8 * I.S) := by ring
  rw [this, ← sub_nonneg]
  have h8 : 0 < 8 * I.S := by positivity
  have : I.kx k 4 - (I.kx (k + 1) 4 + 100 / (8 * I.S)) =
      ((8 * I.S * (I.kx k 4 - (I.S + 1))) - (8 * I.S * (I.kx (k + 1) 4 - (I.S + 1))) - 100) /
        (8 * I.S) := by field_simp; ring
  rw [this]
  apply div_nonneg _ h8.le
  linarith

end Keys

/-! ## The sorted floor -/

/-- The floor entry of the slope-2 slot of pair `k`. -/
def e2 (k : ℕ) : ℚ × List (ℚ × ℚ) := (I.kx k 2, I.slot2 k)

/-- The floor entry of the slope-4 slot of pair `k`. -/
def e4 (k : ℕ) : ℚ × List (ℚ × ℚ) := (I.kx k 4, I.slot4 k)

theorem floorEntries_one (h : I.np = 1) : I.floorEntries = [I.e2 0, I.e4 0] := by
  simp [floorEntries, h, e2, e4]

theorem floorEntries_two (h : I.np = 2) : I.floorEntries = [I.e2 0, I.e4 0, I.e2 1, I.e4 1] := by
  simp [floorEntries, h, List.range_succ, e2, e4]

theorem floorEntries_three (h : I.np = 3) :
    I.floorEntries = [I.e2 0, I.e4 0, I.e2 1, I.e4 1, I.e2 2, I.e4 2] := by
  simp [floorEntries, h, List.range_succ, e2, e4]

section Sorted

variable (hg : I.Good N)
include hg

theorem eps_small : 0 < I.ε ∧ I.ε ≤ 1 / 6400000 := hg.toValid.eps_le

theorem floor_eq_one (h : I.np = 1) : I.floor = I.slot2 0 ++ I.slot4 0 := by
  have h0 : 0 < I.np := by omega
  have a := hg.kx_zero_two h0
  have b := hg.kx_zero_four h0
  rw [abs_le] at a b
  have hs : I.floorEntries.mergeSort (fun a b => decide (a.1 ≤ b.1)) = [I.e2 0, I.e4 0] :=
    mergeSort_eq_of_perm Prod.fst (by rw [floorEntries_one h])
      (by simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
        IsEmpty.forall_iff, implies_true, and_true, List.Pairwise.nil, e2, e4]; linarith)
  simp [floor, hs, e2, e4]

theorem floor_eq_two (h : I.np = 2) :
    I.floor = I.slot2 1 ++ I.slot4 1 ++ I.slot2 0 ++ I.slot4 0 := by
  have h0 : 0 < I.np := by omega
  have a := hg.kx_zero_two h0
  have b := hg.kx_zero_four h0
  have c := hg.kx_two (k := 1) (by omega) le_rfl
  have d := hg.kx_four (k := 1) (by omega) le_rfl
  rw [abs_le] at a b c d
  have hs : I.floorEntries.mergeSort (fun a b => decide (a.1 ≤ b.1)) =
      [I.e2 1, I.e4 1, I.e2 0, I.e4 0] :=
    mergeSort_eq_of_perm Prod.fst (by
      rw [floorEntries_two h]
      exact List.perm_append_comm (l₁ := [I.e2 1, I.e4 1]) (l₂ := [I.e2 0, I.e4 0]))
      (by simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
        IsEmpty.forall_iff, implies_true, and_true, List.Pairwise.nil, e2, e4]
          refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> linarith)
  simp [floor, hs, e2, e4]

theorem floor_eq_three (h : I.np = 3) :
    I.floor = I.slot2 2 ++ I.slot2 1 ++ I.slot4 2 ++ I.slot4 1 ++ I.slot2 0 ++ I.slot4 0 := by
  have h0 : 0 < I.np := by omega
  have a := hg.kx_zero_two h0
  have b := hg.kx_zero_four h0
  have c1 := hg.kx_two (k := 1) (by omega) le_rfl
  have d1 := hg.kx_four (k := 1) (by omega) le_rfl
  have c2 := hg.kx_two (k := 2) (by omega) (by norm_num)
  have d2 := hg.kx_four (k := 2) (by omega) (by norm_num)
  have g2 := hg.kx_two_succ (k := 1) le_rfl (by omega)
  have g4 := hg.kx_four_succ (k := 1) le_rfl (by omega)
  have he := (eps_small hg).1
  rw [abs_le] at a b c1 d1 c2 d2
  have hperm : [I.e2 2, I.e2 1, I.e4 2, I.e4 1, I.e2 0, I.e4 0].Perm
      [I.e2 0, I.e4 0, I.e2 1, I.e4 1, I.e2 2, I.e4 2] := by
    have p1 : [I.e2 0, I.e4 0, I.e2 1, I.e4 1, I.e2 2, I.e4 2].Perm
        (I.e2 2 :: [I.e2 0, I.e4 0, I.e2 1, I.e4 1, I.e4 2]) :=
      List.perm_middle (l₁ := [I.e2 0, I.e4 0, I.e2 1, I.e4 1]) (l₂ := [I.e4 2])
    have p2 : [I.e2 0, I.e4 0, I.e2 1, I.e4 1, I.e4 2].Perm
        (I.e2 1 :: [I.e2 0, I.e4 0, I.e4 1, I.e4 2]) :=
      List.perm_middle (l₁ := [I.e2 0, I.e4 0]) (l₂ := [I.e4 1, I.e4 2])
    have p3 : [I.e2 0, I.e4 0, I.e4 1, I.e4 2].Perm (I.e4 2 :: [I.e2 0, I.e4 0, I.e4 1]) :=
      List.perm_middle (l₁ := [I.e2 0, I.e4 0, I.e4 1]) (l₂ := [])
    have p4 : [I.e2 0, I.e4 0, I.e4 1].Perm (I.e4 1 :: [I.e2 0, I.e4 0]) :=
      List.perm_middle (l₁ := [I.e2 0, I.e4 0]) (l₂ := [])
    exact (p1.trans ((p2.trans ((p3.trans (p4.cons _)).cons _)).cons _)).symm
  have hs : I.floorEntries.mergeSort (fun a b => decide (a.1 ≤ b.1)) =
      [I.e2 2, I.e2 1, I.e4 2, I.e4 1, I.e2 0, I.e4 0] :=
    mergeSort_eq_of_perm Prod.fst (by rw [floorEntries_three h]; exact hperm)
      (by simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
        IsEmpty.forall_iff, implies_true, and_true, List.Pairwise.nil, e2, e4]
          refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
            linarith)
  simp [floor, hs, e2, e4]

end Sorted

end Input

end ArtGallery.Sec5.Corridor

end
