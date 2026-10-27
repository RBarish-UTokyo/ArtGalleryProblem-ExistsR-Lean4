module

public import ArtGallery.Hardness.Sec5.Corridor.CoverFacts

/-!
# Section 5: corridors — the strips below the axes (coverage, part (a))

For pair `k` the **strip piece** `hpSet (I.stripFs k)` is the convex region of the corridor between
the vertical lines through `nxt_k` (the next valley, or `d0`) and `p_k`, above the floor line
`y = H`, below the umbra axis `A_k` and below the left wall `z0_k → nxt_k`
(docs/section5/08_proof_plan.md §9 (a)).

* `Good.strip_subset`: the strip piece lies in the corridor region (convex containment by
  constraints, anchored at a point just above the floor given by `Good.mem_poly_of_vertical`);
* `Good.sees_strip`: hence the stationary guard `p_k` (a point of the piece) sees every point of
  the piece, in any polygon containing the corridor region.

Auxiliary: `Good.bd_above_floor` (boundary points of the corridor polygon strictly between the
doors and above the floor line are at height `≥ H + ρ`), `Good.vert_mem` (points at height
`H + ρ/2` in the middle of the corridor are interior points).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

namespace Input

variable {I : Input} {N : ℚ}

/-! ## Interior points just above the floor -/

section Floorline

variable (hg : I.Good N)
include hg

theorem Good.upper_edges_y {e : Point × Point} (he : e ∈ edgesOf (I.chainAfter.map ratPoint))
    {w : Point} (hw : w ∈ segOf e) : (I.H : ℝ) + I.rhoR ≤ w.2 := by
  have h := edges_affine_le (α := 0) (β := -1) (c := -((I.H : ℝ) + I.rhoR))
    (L := I.chainAfter.map ratPoint) ?_ e he w hw
  · linarith
  intro x hx
  rw [chainAfter_map] at hx
  simp only [List.mem_cons, List.mem_append] at hx
  have hρ := hg.rhoR_pos
  rcases hx with rfl | hx | hx
  · simp
  · have := (hg.upper_box' x hx).2.2.1; linarith
  · rcases hx with rfl | hx
    · simp; linarith
    · simp at hx

/-- Boundary points strictly between the doors and above the floor line are at height `≥ H + ρ`. -/
theorem Good.bd_above_floor {w : Point} (hw : w ∈ I.poly.boundary) (h1 : (I.S : ℝ) < w.1)
    (h2 : w.1 < (I.S : ℝ) + 2) (h3 : (I.H : ℝ) < w.2) : (I.H : ℝ) + I.rhoR ≤ w.2 := by
  rcases poly_boundary_cases hw with ⟨e, he, hwe⟩ | hw | ⟨e, he, hwe⟩ | hw
  · have := hg.floor_edges_le he hwe; linarith
  · exfalso
    have := seg_affine_le (α := -1) (β := 0) (c := -((I.S : ℝ) + 2)) hw
      (by rw [ratPoint_c1']; simp) (by rw [ratPoint_d1']; simp)
    linarith
  · exact hg.upper_edges_y he hwe
  · exfalso
    have := seg_affine_le (α := 1) (β := 0) (c := (I.S : ℝ)) hw
      (by rw [ratPoint_d0']; simp) (by rw [ratPoint_c0']; simp)
    linarith

/-- Points at height `H + ρ/2` in the middle of the corridor are interior points. -/
theorem Good.vert_mem {c : Point} (h1 : (I.S : ℝ) + 4 / 5 ≤ c.1) (h2 : c.1 ≤ (I.S : ℝ) + 7 / 5)
    (h3 : c.2 = (I.H : ℝ) + I.rhoR / 2) : c ∈ I.poly.filled \ I.poly.boundary := by
  have hρ := hg.rhoR_pos
  refine hg.mem_poly_of_vertical h1 h2 (by rw [h3]; linarith) ?_
  intro w hw hwx hwy
  have := hg.bd_above_floor hw (by linarith) (by linarith) hwy
  rw [h3]; linarith

end Floorline

/-! ## The strip pieces -/

/-- The constraints of the strip piece of pair `k`: `x ≤ x(p_k)`, `x ≥ x(nxt_k)`, `y ≥ H`,
below the axis `A_k`, left of the wall `z0_k → nxt_k`. -/
noncomputable def stripFs (I : Input) (k : ℕ) : List Aff :=
  [I.cA (-1) 0 (I.lXR (ratPoint (I.sgPt k))), I.cA 1 0 (-I.lXR (ratPoint (I.nxt k))),
    I.cA 0 1 (8 * I.S), I.cA ((I.hh k : ℚ) : ℝ) (-((I.DD k : ℚ) : ℝ)) (8 * I.S * ((I.gg k : ℚ) : ℝ)),
    Aff.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k))]

theorem negAR_ev (k : ℕ) (z : Point) :
    (I.cA ((I.hh k : ℚ) : ℝ) (-((I.DD k : ℚ) : ℝ)) (8 * I.S * ((I.gg k : ℚ) : ℝ))).ev z =
      -I.AR k z := by
  rw [ev_cA, AR]; ring

theorem mem_strip_iff {k : ℕ} {z : Point} :
    z ∈ hpSet (I.stripFs k) ↔ I.lXR z ≤ I.lXR (ratPoint (I.sgPt k)) ∧
      I.lXR (ratPoint (I.nxt k)) ≤ I.lXR z ∧ -(8 * (I.S : ℝ)) ≤ I.lYR z ∧ I.AR k z ≤ 0 ∧
      0 ≤ ArtGallery.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) z := by
  simp only [hpSet, stripFs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, ev_cA, Aff.ev_det, Set.mem_ofPred_eq]
  simp only [AR]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨by linarith, by linarith, by linarith, by linarith, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨by linarith, by linarith, by linarith, by linarith, h5⟩

section Strip

variable (hg : I.Good N) {k : ℕ} (hk : k < I.np)
include hg hk

/-- Numeric facts about pair `k`. -/
theorem Good.pairR :
    30 ≤ I.lwR k ∧ I.lwR k ≤ 136 * (N : ℝ) + 10 ∧ -790 ≤ I.rwR k ∧ I.rwR k ≤ 810 ∧
      (2 : ℝ) ≤ N ∧ (I.S : ℝ) = 200000 * (N : ℝ) ^ 2 ∧
      |(I.rwR k - I.lwR k) / 2| + 20 ≤ 456 * (N : ℝ) := by
  have h1 := hg.lwE_bound hk
  have h2 := hg.rwE_bound hk
  have h3 := hg.window_apex hk
  have h4 : (2 : ℝ) ≤ N := by exact_mod_cast hg.N_ge
  have h5 : (I.S : ℝ) = 200000 * (N : ℝ) ^ 2 := by exact_mod_cast hg.S_eq
  refine ⟨?_, ?_, ?_, ?_, h4, h5, ?_⟩
  · have := rat_cast_le_of h1.1; simp only [lwR]; push_cast at this; exact this
  · have := rat_cast_le_of h1.2; simp only [lwR]; push_cast at this; exact this
  · have := rat_cast_le_of h2.1; simp only [rwR]; push_cast at this; exact this
  · have := rat_cast_le_of h2.2; simp only [rwR]; push_cast at this; exact this
  · have := rat_cast_le_of h3; simp only [lwR, rwR]; push_cast at this; exact this

omit hk in
/-- The next vertex after `z0_k`: the next valley or `d0`. -/
theorem Good.rl_nxt (_hk : k < I.np) :
    (k + 1 < I.np → I.lXR (ratPoint (I.nxt k)) = (I.rwR k - I.lwR k) / 2 - 54 + 1 / 4 ∧
      I.lYR (ratPoint (I.nxt k)) = (I.lwR k + I.rwR k) / 2 - 54 + 1 / 4) ∧
    (¬ k + 1 < I.np → I.lXR (ratPoint (I.nxt k)) = -(8 * I.S) ∧
      I.lYR (ratPoint (I.nxt k)) = -(8 * I.S) + 24) := by
  constructor
  · intro h
    have hv := hg.rl_valley h (by omega)
    have hr := hg.rwE_succ h
    simp only [nxt, h, ↓reduceIte]
    rw [hv.1, hv.2]
    have : I.rwR (k + 1) = I.rwR k - 108 := by
      simp only [rwR]; rw [hr]; push_cast; ring
    rw [this, show k + 1 - 1 = k by omega]
    constructor <;> ring
  · intro h
    simp only [nxt, h, ↓reduceIte]
    rw [lXR_ratPoint, lYR_ratPoint, lX_d0, lY_d0 hg]
    push_cast; constructor <;> ring

/-- Abscissae of `p_k` and `nxt_k`. -/
theorem Good.rl_strip_ends :
    I.lXR (ratPoint (I.sgPt k)) ≤ 8 * I.S ∧ -(8 * (I.S : ℝ)) ≤ I.lXR (ratPoint (I.nxt k)) ∧
      I.lXR (ratPoint (I.nxt k)) + 50 ≤ I.lXR (ratPoint (I.sgPt k)) ∧
      (1 ≤ k → |I.lXR (ratPoint (I.sgPt k))| ≤ 456 * N) ∧
      (k + 1 < I.np → |I.lXR (ratPoint (I.nxt k))| ≤ 456 * N) := by
  obtain ⟨l1, l2, r1, r2, hN, hS, hw⟩ := hg.pairR hk
  have hSN : 456 * (N : ℝ) + 1000 ≤ 8 * I.S := by rw [hS]; nlinarith
  have hsg : 1 ≤ k → I.lXR (ratPoint (I.sgPt k)) = (I.rwR k - I.lwR (k - 1)) / 2 + 1 / 4 ∧
      |I.lXR (ratPoint (I.sgPt k))| ≤ 456 * N ∧ I.lwR (k - 1) + 108 ≤ I.lwR k := by
    intro hk1
    refine ⟨(hg.rl_sgPt hk hk1).1, ?_, ?_⟩
    · rw [(hg.rl_sgPt hk hk1).1]
      have := hg.window_valley hk hk1
      have h := rat_cast_le_of this; simp only [lwR, rwR]; push_cast at h
      have h' := le_abs_self ((((I.rwE k : ℚ) : ℝ) - ((I.lwE (k - 1) : ℚ) : ℝ)) / 2 + 1 / 4)
      have h'' := neg_abs_le ((((I.rwE k : ℚ) : ℝ) - ((I.lwE (k - 1) : ℚ) : ℝ)) / 2 + 1 / 4)
      rw [abs_le]; constructor <;> linarith
    · have := hg.lwE_succ (k := k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at this
      have := rat_cast_le_of this; simp only [lwR]; push_cast at this; exact this
  have hp0 : k = 0 → I.lXR (ratPoint (I.sgPt k)) = 8 * I.S := by
    rintro rfl; exact rl_sgPt_zero
  obtain ⟨hn1, hn2⟩ := hg.rl_nxt hk
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw2
  have hnw : k + 1 < I.np → |I.lXR (ratPoint (I.nxt k))| ≤ 456 * N := by
    intro h; rw [(hn1 h).1, abs_le]
    -- the next apex is in the window
    have h' := hg.pairR (k := k + 1) h
    have hr := hg.rwE_succ h
    have hl := hg.lwE_succ h
    have hr' : I.rwR (k + 1) = I.rwR k - 108 := by simp only [rwR]; rw [hr]; push_cast; ring
    have hl' : I.lwR k + 108 ≤ I.lwR (k + 1) := by
      have := rat_cast_le_of hl; simp only [lwR]; push_cast at this; exact this
    obtain ⟨-, -, -, -, -, -, hw'⟩ := h'
    have hw3 : |(I.rwR (k + 1) - I.lwR (k + 1)) / 2| ≤ 456 * N - 20 := by linarith
    rw [abs_le] at hw3
    constructor <;> linarith
  refine ⟨?_, ?_, ?_, fun h => (hsg h).2.1, hnw⟩
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [hp0 h0]
    · have := (hsg h0).2.1; rw [abs_le] at this; linarith
  · by_cases h : k + 1 < I.np
    · have := hnw h; rw [abs_le] at this; linarith
    · rw [(hn2 h).1]
  · by_cases h : k + 1 < I.np
    · rw [(hn1 h).1]
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [hp0 h0]; linarith
      · rw [(hsg h0).1]; linarith [(hsg h0).2.2]
    · rw [(hn2 h).1]
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [hp0 h0]; linarith
      · have := (hsg h0).2.1; rw [abs_le] at this; linarith

/-- The upper-wall vertices `z1, n1, n0, z0` are strictly above the axis. -/
theorem Good.AR_feature_pos :
    0 < I.AR k (ratPoint (I.z1 k)) ∧ 0 < I.AR k (ratPoint (I.n1 k)) ∧
      0 < I.AR k (ratPoint (I.n0 k)) ∧ 0 < I.AR k (ratPoint (I.z0 k)) := by
  obtain ⟨-, -, -, -, -, -, hw0⟩ := hg.pairR hk
  have hw : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw
  have b1 := hg.rl_z1 hk
  have b0 := hg.rl_z0 hk
  have c1 := hg.rl_n1 hk
  have c0 := hg.rl_n0 hk
  rw [abs_le] at c1 c0
  refine ⟨hg.AR_pos_of hk ?_ ?_, hg.AR_pos_of hk ?_ ?_, hg.AR_pos_of hk ?_ ?_,
    hg.AR_pos_of hk ?_ ?_⟩
  all_goals first
    | (rw [abs_le]; constructor <;> linarith)
    | linarith

/-- The left wall `z0_k → nxt_k` in local coordinates. -/
theorem Good.wall_det (P : Point) :
    (k + 1 < I.np → 64 * (I.S : ℝ) ^ 2 * ArtGallery.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) P =
      203 / 4 * (I.lwR k - (I.lYR P - I.lXR P))) ∧
    (¬ k + 1 < I.np → 64 * (I.S : ℝ) ^ 2 * ArtGallery.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) P =
      8 * I.S * (I.lwR k - (I.lYR P - I.lXR P)) -
        ((I.rwR k - I.lwR k) / 2 - 3) * (I.lYR P - ((I.lwR k + I.rwR k) / 2 - 3)) -
        (I.lXR P - ((I.rwR k - I.lwR k) / 2 - 3)) * (24 - ((I.lwR k + I.rwR k) / 2 - 3))) := by
  obtain ⟨hn1, hn2⟩ := hg.rl_nxt hk
  have b0 := hg.rl_z0 hk
  have key := det_lXR (I := I) (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) P
  rw [b0.1, b0.2] at key
  constructor
  · intro h; rw [key, (hn1 h).1, (hn1 h).2]; ring
  · intro h; rw [key, (hn2 h).1, (hn2 h).2]; ring

/-- The wall inequality for points of the window below `ζ = ℓ − 1`. -/
theorem Good.wall_of_window {P : Point} (hX : |I.lXR P| ≤ 1000 * N) (hY : |I.lYR P| ≤ 1000 * N)
    (hζ : I.lYR P - I.lXR P ≤ I.lwR k - 1) :
    0 < ArtGallery.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) P := by
  obtain ⟨l1, l2, r1, r2, hN, hS, hw⟩ := hg.pairR hk
  obtain ⟨w1, w2⟩ := hg.wall_det hk P
  have h64 : (0 : ℝ) < 64 * (I.S : ℝ) ^ 2 := by rw [hS]; positivity
  refine pos_of_mul_pos_right ?_ h64.le
  rw [mul_comm] at w1 w2
  by_cases h : k + 1 < I.np
  · rw [mul_comm, w1 h]; nlinarith
  · rw [mul_comm, w2 h]
    have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
    rw [abs_le] at hw2 hX hY
    set X0 := (I.rwR k - I.lwR k) / 2 - 3 with hX0d
    set Y0 := (I.lwR k + I.rwR k) / 2 - 3 with hY0d
    have hX0 : |X0| ≤ 456 * N := by rw [abs_le]; constructor <;> linarith
    have hY0 : |Y0| ≤ 500 * N := by rw [abs_le]; constructor <;> nlinarith
    have h1 : |X0 * (I.lYR P - Y0)| ≤ 456 * N * (1500 * N) := by
      rw [abs_mul]; exact mul_le_mul hX0 (by rw [abs_le] at hY0 ⊢; constructor <;> linarith)
        (abs_nonneg _) (by linarith)
    have h2 : |(I.lXR P - X0) * (24 - Y0)| ≤ 1500 * N * (600 * N) := by
      rw [abs_le] at hX0
      rw [abs_mul]; exact mul_le_mul (by rw [abs_le]; constructor <;> linarith)
        (by rw [abs_le] at hY0 ⊢; constructor <;> nlinarith) (abs_nonneg _) (by linarith)
    rw [abs_le] at h1 h2
    have h3 : 8 * (I.S : ℝ) * 1 ≤ 8 * I.S * (I.lwR k - (I.lYR P - I.lXR P)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by rw [hS]; positivity)
    have h4 : 456 * (N : ℝ) * (1500 * N) + 1500 * N * (600 * N) < 8 * I.S * 1 := by
      rw [hS]; nlinarith
    linarith

/-- The wall inequality at the anchor (a far point below the corridor's middle). -/
theorem Good.strip_anchor_det (X : ℝ) (hXa : |X| ≤ 1000 * N) {c : Point} (cX : I.lXR c = X)
    (cY : I.lYR c = -(8 * I.S) + 6) :
    0 < ArtGallery.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) c := by
  obtain ⟨l1, l2, r1, r2, hN, hS, hw⟩ := hg.pairR hk
  obtain ⟨w1, w2⟩ := hg.wall_det hk c
  have h64 : (0 : ℝ) < 64 * (I.S : ℝ) ^ 2 := by rw [hS]; positivity
  refine pos_of_mul_pos_right ?_ h64.le
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw2 hXa
  have hS1 : (100000 : ℝ) * N ≤ I.S := by rw [hS]; nlinarith
  by_cases h : k + 1 < I.np
  · rw [w1 h, cX, cY]; nlinarith
  · rw [w2 h, cX, cY]
    set X0 := (I.rwR k - I.lwR k) / 2 - 3 with hX0d
    set Y0 := (I.lwR k + I.rwR k) / 2 - 3 with hY0d
    set A : ℝ := 8 * I.S with hA
    have hX0 : |X0| ≤ 456 * N := by rw [abs_le]; constructor <;> linarith
    have hY0 : |Y0| ≤ 500 * N := by rw [abs_le]; constructor <;> nlinarith
    have hY1 : |-A + 6 - Y0| ≤ A + 600 * N := by
      rw [abs_le] at hY0 ⊢; constructor <;> linarith
    have h1 : |X0 * (-A + 6 - Y0)| ≤ 456 * N * (A + 600 * N) := by
      rw [abs_mul]; exact mul_le_mul hX0 hY1 (abs_nonneg _) (by linarith)
    have h2 : |(X - X0) * (24 - Y0)| ≤ 1500 * N * (600 * N) := by
      rw [abs_le] at hX0
      rw [abs_mul]; exact mul_le_mul (by rw [abs_le]; constructor <;> linarith)
        (by rw [abs_le] at hY0 ⊢; constructor <;> nlinarith) (abs_nonneg _) (by linarith)
    rw [abs_le] at h1 h2
    have hA1 : 800000 * (N : ℝ) ≤ A := by rw [hA]; linarith
    have h3 : A * (A / 2) ≤ A * (I.lwR k - (-A + 6 - X)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h4 : 456 * (N : ℝ) * (A + 600 * N) + 1500 * N * (600 * N) < A * (A / 2) := by nlinarith
    linarith

/-- The anchor of the strip piece: a point just above the floor, strictly inside the piece. -/
theorem Good.strip_anchor : ∃ c : Point, c ∈ hpOpen (I.stripFs k) ∧
    c ∈ I.poly.filled \ I.poly.boundary := by
  obtain ⟨l1, l2, r1, r2, hN, hS, hw⟩ := hg.pairR hk
  obtain ⟨e1, e2, e3, e4, e5⟩ := hg.rl_strip_ends hk
  obtain ⟨hn1, hn2⟩ := hg.rl_nxt hk
  have hSpos : (0 : ℝ) < I.S := by rw [hS]; positivity
  have hw2 : |(I.rwR k - I.lwR k) / 2| ≤ 456 * N - 20 := by linarith
  rw [abs_le] at hw2
  set lo : ℝ := if k + 1 < I.np then I.lXR (ratPoint (I.nxt k)) else -(1000 * N) with hlo
  set hi : ℝ := if k = 0 then 1000 * N else I.lXR (ratPoint (I.sgPt k)) with hhi
  have hlo1 : I.lXR (ratPoint (I.nxt k)) ≤ lo := by
    rw [hlo]; split_ifs with h
    · exact le_rfl
    · rw [(hn2 h).1]; nlinarith
  have hhi1 : hi ≤ I.lXR (ratPoint (I.sgPt k)) := by
    rw [hhi]; split_ifs with h
    · subst h; rw [rl_sgPt_zero]; nlinarith
    · exact le_rfl
  have hlohi : lo + 50 ≤ hi := by
    rw [hlo, hhi]
    by_cases h : k + 1 < I.np
    · by_cases h' : k = 0
      · simp only [eq_true h, eq_true h', ↓reduceIte]; have := e5 h; rw [abs_le] at this; linarith
      · simp only [eq_true h, eq_false h', ↓reduceIte]; linarith
    · by_cases h' : k = 0
      · simp only [eq_false h, eq_true h', ↓reduceIte]; linarith
      · simp only [eq_false h, eq_false h', ↓reduceIte]
        have := e4 (by omega); rw [abs_le] at this; linarith
  have hloB : -(1000 * (N : ℝ)) ≤ lo := by
    rw [hlo]; split_ifs with h
    · have := e5 h; rw [abs_le] at this; linarith
    · exact le_rfl
  have hhiB : hi ≤ 1000 * N := by
    rw [hhi]; split_ifs with h
    · exact le_rfl
    · have := e4 (by omega); rw [abs_le] at this; linarith
  set X : ℝ := (lo + hi) / 2 with hX
  let c : Point := ((I.S : ℝ) + 1 + X / (8 * I.S), (I.H : ℝ) + I.rhoR / 2)
  have cX : I.lXR c = X := by simp only [lXR, c]; field_simp; ring
  have cY : I.lYR c = -(8 * I.S) + 6 := by simp only [lYR, c, rhoR_eq]; field_simp; ring
  refine ⟨c, ?_, ?_⟩
  · have hmem : I.lXR c < I.lXR (ratPoint (I.sgPt k)) ∧ I.lXR (ratPoint (I.nxt k)) < I.lXR c ∧
        -(8 * (I.S : ℝ)) < I.lYR c ∧ I.AR k c < 0 ∧
        0 < ArtGallery.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) c := by
      refine ⟨by rw [cX]; linarith, by rw [cX]; linarith, by rw [cY]; linarith, ?_, ?_⟩
      · obtain ⟨E, hE, hEb⟩ := hg.AR_eq hk c
        obtain ⟨hD1, hD2⟩ := hg.DDR_bounds hk
        have hh := hg.hhR_abs hk
        rw [abs_le] at hEb
        have hXa : |X| ≤ 1000 * N := by rw [abs_le]; constructor <;> linarith
        have hhX : |((I.hh k : ℚ) : ℝ) * I.lXR c| ≤ (3 * N + 50) * (1000 * N) := by
          rw [abs_mul, cX]; exact mul_le_mul hh hXa (abs_nonneg _) (by linarith)
        rw [abs_le] at hhX
        have hf : I.lYR c - ((I.lwR k + I.rwR k) / 2 - 16) ≤ -(7 * (I.S : ℝ)) := by
          rw [cY]
          have : (1000 : ℝ) ≤ I.S := by rw [hS]; nlinarith
          linarith
        have h7 : ((I.DD k : ℚ) : ℝ) * (I.lYR c - ((I.lwR k + I.rwR k) / 2 - 16)) ≤
            (I.S : ℝ) * (-(7 * (I.S : ℝ))) :=
          (mul_le_mul_of_nonpos_right hD1 (by linarith)).trans
            (mul_le_mul_of_nonneg_left hf hSpos.le)
        have h8 : (3 * (N : ℝ) + 50) * (1000 * N) + 4 * (17 * N + 100) * (14 * N + 50) <
            7 * (I.S : ℝ) * I.S := by
          rw [hS]; nlinarith
        rw [hE]; nlinarith
      · exact hg.strip_anchor_det hk X (by rw [abs_le]; constructor <;> linarith) cX cY
    obtain ⟨h1, h2, h3, h4, h5⟩ := hmem
    simp only [hpOpen, stripFs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, ev_cA, Aff.ev_det, Set.mem_ofPred_eq]
    simp only [AR] at h4
    exact ⟨by linarith, by linarith, by linarith, by linarith, h5⟩
  · have hXa : |X| ≤ 1000 * N := by rw [abs_le]; constructor <;> linarith
    rw [abs_le] at hXa
    refine hg.vert_mem ?_ ?_ rfl
    · show (I.S : ℝ) + 4 / 5 ≤ (I.S : ℝ) + 1 + X / (8 * I.S)
      have : -(1 / 5 : ℝ) ≤ X / (8 * I.S) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      linarith
    · show (I.S : ℝ) + 1 + X / (8 * I.S) ≤ (I.S : ℝ) + 7 / 5
      have : X / (8 * I.S) ≤ 2 / 5 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith

/-- **The strip piece lies in the corridor region.** -/
theorem Good.strip_subset : hpSet (I.stripFs k) ⊆ I.poly.filled := by
  obtain ⟨c, hc, hcK⟩ := hg.strip_anchor hk
  obtain ⟨e1, e2, e3, e4, e5⟩ := hg.rl_strip_ends hk
  obtain ⟨a1, a2, a3, a4⟩ := hg.AR_feature_pos hk
  have zp0 := (hg.rl_zp hk).2.2.2.2
  have sg0 := hg.AR_sgPt hk
  have m1 : I.cA (-1) 0 (I.lXR (ratPoint (I.sgPt k))) ∈ I.stripFs k := by simp [stripFs]
  have m2 : I.cA 1 0 (-I.lXR (ratPoint (I.nxt k))) ∈ I.stripFs k := by simp [stripFs]
  have m3 : I.cA 0 1 (8 * I.S) ∈ I.stripFs k := by simp [stripFs]
  have m4 : I.cA ((I.hh k : ℚ) : ℝ) (-((I.DD k : ℚ) : ℝ)) (8 * I.S * ((I.gg k : ℚ) : ℝ)) ∈
      I.stripFs k := by simp [stripFs]
  have m5 : Aff.det (ratPoint (I.z0 k)) (ratPoint (I.nxt k)) ∈ I.stripFs k := by simp [stripFs]
  refine hpSet_subset_filled hg.poly_simple ?_ hc (hpOpen_subset_hpSet _ hc) hcK.1 hcK.2
  refine hg.bd_check hk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine hg.floor_check m3 ?_
    intro w hw; rw [ev_cA]; have := (lYR_le_floor_iff hg).2 hw; linarith
  · refine ⟨_, m1, ?_, ?_⟩ <;> simp only [ev_cA, lXR_c1', lXR_d1'] <;> linarith
  · refine ⟨_, m2, ?_, ?_⟩ <;> simp only [ev_cA, lXR_c0', lXR_d0'] <;> linarith
  · refine ⟨_, m1, fun v hv => ?_⟩
    rw [ev_cA]; have := (lXR_le_iff' hg).2 (show (ratPoint (I.sgPt k)).1 ≤ (ratPoint v).1 by
      simp only [ratPoint]; exact_mod_cast hv)
    linarith
  · refine ⟨_, m2, fun v hv => ?_⟩
    rw [ev_cA]; have := (lXR_le_iff' hg).2 (show (ratPoint v).1 ≤ (ratPoint (I.nxt k)).1 by
      simp only [ratPoint]; exact_mod_cast hv)
    linarith
  · exact ⟨_, m4, by rw [negAR_ev]; linarith, by rw [negAR_ev]; linarith⟩
  · exact ⟨_, m4, by rw [negAR_ev]; linarith, by rw [negAR_ev]; linarith⟩
  · exact ⟨_, m4, by rw [negAR_ev]; linarith, by rw [negAR_ev]; linarith⟩
  · exact ⟨_, m4, by rw [negAR_ev]; linarith, by rw [negAR_ev]; linarith⟩
  · exact ⟨_, m4, by rw [negAR_ev]; linarith, by rw [negAR_ev]; linarith⟩
  · exact ⟨_, m5, by simp [ArtGallery.det], by simp [ArtGallery.det]⟩

/-- The stationary guard is a point of its strip piece. -/
theorem Good.sgPt_mem_strip : ratPoint (I.sgPt k) ∈ hpSet (I.stripFs k) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := hg.rl_strip_ends hk
  have b0 := hg.rl_z0 hk
  obtain ⟨hn1, hn2⟩ := hg.rl_nxt hk
  obtain ⟨l1, l2, r1, r2, hN, hS, hw⟩ := hg.pairR hk
  rw [mem_strip_iff]
  refine ⟨le_rfl, by linarith, ?_, (hg.AR_sgPt hk).le, ?_⟩
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      have := hg.lY_sgPt_zero_abs hk
      have h' := rat_cast_le_of this; push_cast at h'
      rw [lYR_ratPoint]; rw [abs_le] at h'; nlinarith
    · have := (hg.rl_sgPt hk h0).2; rw [abs_le] at this
      have hS8 : (1000 : ℝ) ≤ I.S := by rw [hS]; nlinarith
      linarith
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      have hy := hg.lY_sgPt_zero_abs hk
      have h' := rat_cast_le_of hy; push_cast at h'
      rw [← lYR_ratPoint] at h'
      have hx := rl_sgPt_zero (I := I)
      obtain ⟨w1, w2⟩ := hg.wall_det hk (ratPoint (I.sgPt 0))
      have h64 : (0 : ℝ) < 64 * (I.S : ℝ) ^ 2 := by rw [hS]; positivity
      refine nonneg_of_mul_nonneg_right ?_ h64
      rw [mul_comm]
      have hw2 : |(I.rwR 0 - I.lwR 0) / 2| ≤ 456 * N - 20 := by linarith
      rw [abs_le] at hw2 h'
      by_cases h : 0 + 1 < I.np
      · rw [mul_comm, w1 h, hx]; nlinarith
      · rw [mul_comm, w2 h, hx]
        set X0 := (I.rwR 0 - I.lwR 0) / 2 - 3 with hX0d
        set Y0 := (I.lwR 0 + I.rwR 0) / 2 - 3 with hY0d
        set A : ℝ := 8 * I.S with hA
        set Yp := I.lYR (ratPoint (I.sgPt 0)) with hYp
        have hX0 : |X0| ≤ 456 * N := by rw [abs_le]; constructor <;> linarith
        have h1 : |X0 * (Yp - Y0)| ≤ 456 * N * (1500 * N) := by
          rw [abs_mul]; exact mul_le_mul hX0 (by rw [abs_le]; constructor <;> nlinarith)
            (abs_nonneg _) (by linarith)
        have h2 : |(A - X0) * (24 - Y0)| ≤ (A + 456 * N) * (600 * N) := by
          rw [abs_le] at hX0
          rw [abs_mul]; exact mul_le_mul (by rw [abs_le]; constructor <;> linarith)
            (by rw [abs_le]; constructor <;> nlinarith) (abs_nonneg _) (by linarith)
        rw [abs_le] at h1 h2
        have hA1 : 800000 * (N : ℝ) ^ 2 ≤ A := by rw [hA, hS]; nlinarith
        have h3 : A * (A / 2) ≤ A * (I.lwR 0 - (Yp - A)) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by nlinarith)
        have h4 : 456 * (N : ℝ) * (1500 * N) + (A + 456 * N) * (600 * N) < A * (A / 2) := by
          nlinarith
        linarith
    · obtain ⟨hx, hy⟩ := hg.rl_sgPt hk h0
      have hl := hg.lwE_succ (k := k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at hl
      have hl' : I.lwR (k - 1) + 108 ≤ I.lwR k := by
        have := rat_cast_le_of hl; simp only [lwR]; push_cast at this; exact this
      have hp := e4 h0
      rw [abs_le] at hy
      refine (hg.wall_of_window hk (by rw [abs_le] at hp ⊢; constructor <;> linarith) ?_ ?_).le
      · rw [abs_le]; constructor <;> linarith
      · rw [hx]; linarith

/-- **The stationary guard sees its strip piece.** -/
theorem Good.sees_strip {P : Polygon} (hsub : I.poly.filled ⊆ P.filled) {z : Point}
    (hz : z ∈ hpSet (I.stripFs k)) : P.Sees (ratPoint (I.sgPt k)) z :=
  sees_of_hpSet ((hg.strip_subset hk).trans hsub) (hg.sgPt_mem_strip hk) hz

end Strip

end Input

end ArtGallery.Sec5.Corridor

end
