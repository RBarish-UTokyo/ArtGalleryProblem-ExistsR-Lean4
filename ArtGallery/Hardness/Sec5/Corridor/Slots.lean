module

public import ArtGallery.Hardness.Sec5.Corridor.Stationary

/-!
# Section 5: corridors — the slot witnesses

The tips `q_a = slotTip k 2`, `q_b = slotTip k 4` of the floor witness slots of pair `k` are
convex vertices of `P`; their cones are thin wedges along the lines of slope 2 resp. 4 through
`p_k`.  With `u₂(x) = x.1 − (x.2 − H)/2`, `u₄(x) = x.1 − (x.2 − H)/4`:

* `cone(q_a) = {κ₂ − ε(x.2 − H + 1/8) ≤ u₂(x) ≤ κ₂}` (`cone2_iff`),
* `cone(q_b) = {κ₄ ≤ u₄(x) ≤ κ₄ + (ε/2)(x.2 − H + 1/4)}` (`cone4_iff`),

where `κ_s = kx k s` (the key of the slot; `u_s(p_k) = κ_s`).  Consequences:

* **the visibility sets of the tips lie in the corridor** (`Good.sees_tip2_mem`,
  `Good.sees_tip4_mem`: the cones miss the window and the entrance); in particular no point
  outside the corridor sees a tip;
* **other stationary guards do not see the tips** (`Good.not_sees_tip2_sg`,
  `Good.not_sees_tip4_sg`: `u_s(p_j) = κ_s(j)` is at distance `≥ 100ε` from `κ_s(k)`);
* **the slope-4 witnesses of different pairs have disjoint visibility sets**
  (`Good.not_sees_tip4_tip4`).
-/

@[expose] public section

namespace ArtGallery.Sec5.Corridor

open ArtGallery Set Polygon

/-! ## The slot cones in coordinates -/

section Cones

variable (κ H e : ℝ)

theorem det_tip2_right (x : Point) :
    det (κ - 1 / 16, H - 1 / 8) (κ, H) x = -(1 / 8) * ((x.1 - (x.2 - H) / 2) - κ) := by
  simp only [det]; ring

theorem det_tip2_left (x : Point) :
    det (κ - e / 8, H) (κ - 1 / 16, H - 1 / 8) x =
      (1 / 8) * ((x.1 - (x.2 - H) / 2) - κ + e * (x.2 - H + 1 / 8)) := by
  simp only [det]; ring

theorem det_tip4_left (x : Point) :
    det (κ, H) (κ - 1 / 16, H - 1 / 4) x = (1 / 4) * ((x.1 - (x.2 - H) / 4) - κ) := by
  simp only [det]; ring

theorem det_tip4_right (x : Point) :
    det (κ - 1 / 16, H - 1 / 4) (κ + e / 8, H) x =
      -(1 / 4) * ((x.1 - (x.2 - H) / 4) - κ) + e / 8 * (x.2 - H + 1 / 4) := by
  simp only [det]; ring

variable {κ H e}

/-- The cone of a slope-2 tip. -/
theorem cone2_iff {x : Point} :
    x ∈ cornerCone (κ - e / 8, H) (κ - 1 / 16, H - 1 / 8) (κ, H) ↔
      κ - e * (x.2 - H + 1 / 8) ≤ x.1 - (x.2 - H) / 2 ∧ x.1 - (x.2 - H) / 2 ≤ κ := by
  simp only [cornerCone, mem_ofPred_eq, det_tip2_left, det_tip2_right]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

/-- The cone of a slope-4 tip. -/
theorem cone4_iff {x : Point} :
    x ∈ cornerCone (κ, H) (κ - 1 / 16, H - 1 / 4) (κ + e / 8, H) ↔
      κ ≤ x.1 - (x.2 - H) / 4 ∧ x.1 - (x.2 - H) / 4 - κ ≤ e / 2 * (x.2 - H + 1 / 4) := by
  simp only [cornerCone, mem_ofPred_eq, det_tip4_left, det_tip4_right]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

end Cones

/-- Casting a rational inequality. -/
theorem rat_cast_le_of {a b : ℚ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h

namespace Input

variable {I : Input} {N : ℚ}

/-- A vertex of the corridor chains lies in the corridor region. -/
theorem mem_poly_of_mem {x : ℚ × ℚ} (hx : x ∈ I.chainBefore ++ I.chainAfter) :
    ratPoint x ∈ I.poly.filled := by
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
  have hn : I.poly.n = (I.chainBefore ++ I.chainAfter).length := poly_n
  have hvi : I.poly.vtx i = ratPoint x := by
    rw [poly_vtx, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
    simp [hix]
  exact Or.inl ⟨i, by rw [hn]; exact hi, by rw [← hvi]; exact Geometry.left_mem_segment _ _⟩

/-- The stationary guard `p_j` lies on the slot lines of its own pair: `u_s(p_j) = κ_s(j)`. -/
theorem sgPt_on_slot2 (j : ℕ) :
    ((I.sgPt j).1 : ℝ) - (((I.sgPt j).2 : ℝ) - I.H) / 2 = (I.kx j 2 : ℝ) := by
  simp only [kx]; push_cast; ring

/-- The stationary guard `p_j` lies on the slope-4 slot line of its own pair. -/
theorem sgPt_on_slot4 (j : ℕ) :
    ((I.sgPt j).1 : ℝ) - (((I.sgPt j).2 : ℝ) - I.H) / 4 = (I.kx j 4 : ℝ) := by
  simp only [kx]; push_cast; ring

/-- The three vertices of the slope-2 slot of pair `k` over `ℝ`. -/
theorem slot2_ratPoint (k : ℕ) :
    ratPoint (I.kx k 2 - I.ε / 8, I.H) = ((I.kx k 2 : ℝ) - (I.ε : ℝ) / 8, (I.H : ℝ)) ∧
      ratPoint (I.slotTip k 2) = ((I.kx k 2 : ℝ) - 1 / 16, (I.H : ℝ) - 1 / 8) ∧
      ratPoint (I.kx k 2, I.H) = ((I.kx k 2 : ℝ), (I.H : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [ratPoint, slotTip]; norm_num

/-- The three vertices of the slope-4 slot of pair `k` over `ℝ`. -/
theorem slot4_ratPoint (k : ℕ) :
    ratPoint (I.kx k 4, I.H) = ((I.kx k 4 : ℝ), (I.H : ℝ)) ∧
      ratPoint (I.slotTip k 4) = ((I.kx k 4 : ℝ) - 1 / 16, (I.H : ℝ) - 1 / 4) ∧
      ratPoint (I.kx k 4 + I.ε / 8, I.H) = ((I.kx k 4 : ℝ) + (I.ε : ℝ) / 8, (I.H : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [ratPoint, slotTip]; norm_num

section Keys

variable (hg : I.Good N)
include hg

/-- Real bounds on the slope-2 keys: every key lies in `[S + 1/2 − 1/1000, S + 3/2 + 1/1000]`. -/
theorem Good.kx2_real {k : ℕ} (hk : k < I.np) :
    (I.S : ℝ) + 1 / 2 - 1 / 1000 ≤ (I.kx k 2 : ℝ) ∧ (I.kx k 2 : ℝ) ≤ (I.S : ℝ) + 3 / 2 + 1 / 1000 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · have h := hg.kx_zero_two hk
    rw [abs_le] at h
    constructor
    · have h' : (I.S + 1 / 2 - 1 / 1000 : ℚ) ≤ I.kx 0 2 := by linarith
      have := rat_cast_le_of h'; push_cast at this; linarith
    · have h' : I.kx 0 2 ≤ I.S + 3 / 2 + 1 / 1000 := by linarith
      have := rat_cast_le_of h'; push_cast at this; linarith
  · have h := hg.kx_two hk hk1
    rw [abs_le] at h
    constructor
    · have h' : (I.S + 1 / 2 - 1 / 1000 : ℚ) ≤ I.kx k 2 := by linarith
      have := rat_cast_le_of h'; push_cast at this; linarith
    · have h' : I.kx k 2 ≤ I.S + 3 / 2 + 1 / 1000 := by linarith
      have := rat_cast_le_of h'; push_cast at this; linarith

/-- Real bounds on the slope-4 keys: every key lies in `[S + 3/4 − 1/1000, S + 7/4 + 1/1000]`. -/
theorem Good.kx4_real {k : ℕ} (hk : k < I.np) :
    (I.S : ℝ) + 3 / 4 - 1 / 1000 ≤ (I.kx k 4 : ℝ) ∧ (I.kx k 4 : ℝ) ≤ (I.S : ℝ) + 7 / 4 + 1 / 1000 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · have h := hg.kx_zero_four hk
    rw [abs_le] at h
    constructor
    · have h' : (I.S + 3 / 4 - 1 / 1000 : ℚ) ≤ I.kx 0 4 := by linarith
      have := rat_cast_le_of h'; push_cast at this; linarith
    · have h' : I.kx 0 4 ≤ I.S + 7 / 4 + 1 / 1000 := by linarith
      have := rat_cast_le_of h'; push_cast at this; linarith
  · have h := hg.kx_four hk hk1
    rw [abs_le] at h
    constructor
    · have h' : (I.S + 3 / 4 - 1 / 1000 : ℚ) ≤ I.kx k 4 := by linarith
      have := rat_cast_le_of h'; push_cast at this; linarith
    · have h' : I.kx k 4 ≤ I.S + 7 / 4 + 1 / 1000 := by linarith
      have := rat_cast_le_of h'; push_cast at this; linarith

/-- The keys of different pairs are far apart. -/
theorem Good.kx_sep {s : ℚ} (hs : s = 2 ∨ s = 4) {j k : ℕ} (hjk : j < k) (hk : k < I.np) :
    I.kx k s + 100 * I.ε ≤ I.kx j s := by
  have he := (eps_small hg)
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · -- `j = 0` against a later pair
    rcases hs with rfl | rfl
    · have a := hg.kx_zero_two (by omega)
      have b := hg.kx_two hk (by omega)
      rw [abs_le] at a b; linarith [he.2]
    · have a := hg.kx_zero_four (by omega)
      have b := hg.kx_four hk (by omega)
      rw [abs_le] at a b; linarith [he.2]
  · -- both later pairs: chain of steps
    induction k with
    | zero => omega
    | succ k ih =>
      have step : I.kx (k + 1) s + 100 * I.ε ≤ I.kx k s := by
        rcases hs with rfl | rfl
        · exact hg.kx_two_succ (by omega) hk
        · exact hg.kx_four_succ (by omega) hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with h | h
      · have := ih h (by omega); linarith [he.1]
      · subst h; exact step

end Keys

/-! ## The visibility sets of the tips -/

section Tips

variable (hg : I.Good N) {P : Polygon} {a b : ℕ} (hP : P.Simple) (hL : P.InteriorLeft)
  (hC : CorridorAt P I a b) {k : ℕ} (hk : k < I.np)
include hg hP hL hC hk

set_option linter.unusedSectionVars false in
/-- The slope-2 tip as a vertex of `P` with its neighbours. -/
theorem Good.tip2_vtx : ∃ i < P.n, P.vtx i = ratPoint (I.slotTip k 2) ∧
    P.vtx ((i + P.n - 1) % P.n) = ratPoint (I.kx k 2 - I.ε / 8, I.H) ∧
    P.vtx ((i + 1) % P.n) = ratPoint (I.kx k 2, I.H) := by
  have hn : 0 < P.n := by have := hP.1; omega
  obtain ⟨B₁, B₂, hB⟩ := chainBefore_infix_slot2 hk
  obtain ⟨h1, h2, h3, -, -⟩ := vtx_triple (x := (I.kx k 2 - I.ε / 8, I.H))
    (y := I.slotTip k 2) (z := (I.kx k 2, I.H)) hn hC.before (by rw [hB]; rfl)
  exact ⟨_, Nat.mod_lt _ hn, h1, h2, h3⟩

set_option linter.unusedSectionVars false in
/-- The slope-4 tip as a vertex of `P` with its neighbours. -/
theorem Good.tip4_vtx : ∃ i < P.n, P.vtx i = ratPoint (I.slotTip k 4) ∧
    P.vtx ((i + P.n - 1) % P.n) = ratPoint (I.kx k 4, I.H) ∧
    P.vtx ((i + 1) % P.n) = ratPoint (I.kx k 4 + I.ε / 8, I.H) := by
  have hn : 0 < P.n := by have := hP.1; omega
  obtain ⟨B₁, B₂, hB⟩ := chainBefore_infix_slot4 hk
  obtain ⟨h1, h2, h3, -, -⟩ := vtx_triple (x := (I.kx k 4, I.H))
    (y := I.slotTip k 4) (z := (I.kx k 4 + I.ε / 8, I.H)) hn hC.before (by rw [hB]; rfl)
  exact ⟨_, Nat.mod_lt _ hn, h1, h2, h3⟩

/-- **Cone of the slope-2 tip**: every point seeing `q_a` lies in its cone. -/
theorem Good.sees_tip2_cone {x : Point} (hx : P.Sees x (ratPoint (I.slotTip k 2))) :
    (I.kx k 2 : ℝ) - (I.ε : ℝ) * (x.2 - I.H + 1 / 8) ≤ x.1 - (x.2 - I.H) / 2 ∧
      x.1 - (x.2 - I.H) / 2 ≤ (I.kx k 2 : ℝ) := by
  obtain ⟨i, hi, h1, h2, h3⟩ := hg.tip2_vtx hP hL hC hk
  obtain ⟨r1, r2, r3⟩ := slot2_ratPoint (I := I) k
  rw [r1] at h2; rw [r2] at h1; rw [r3] at h3
  have hconv : 0 < det ((I.kx k 2 : ℝ) - (I.ε : ℝ) / 8, (I.H : ℝ))
      ((I.kx k 2 : ℝ) - 1 / 16, (I.H : ℝ) - 1 / 8) ((I.kx k 2 : ℝ), (I.H : ℝ)) := by
    rw [det_tip2_left]; simp only; have := hg.eps_real.1; nlinarith
  rw [r2] at hx
  exact cone2_iff.1 (sees_subset_cone' hP hL hi h2 h1 h3 hconv hx)

/-- **Cone of the slope-4 tip**: every point seeing `q_b` lies in its cone. -/
theorem Good.sees_tip4_cone {x : Point} (hx : P.Sees x (ratPoint (I.slotTip k 4))) :
    (I.kx k 4 : ℝ) ≤ x.1 - (x.2 - I.H) / 4 ∧
      x.1 - (x.2 - I.H) / 4 - I.kx k 4 ≤ (I.ε : ℝ) / 2 * (x.2 - I.H + 1 / 4) := by
  obtain ⟨i, hi, h1, h2, h3⟩ := hg.tip4_vtx hP hL hC hk
  obtain ⟨r1, r2, r3⟩ := slot4_ratPoint (I := I) k
  rw [r1] at h2; rw [r2] at h1; rw [r3] at h3
  have hconv : 0 < det ((I.kx k 4 : ℝ), (I.H : ℝ))
      ((I.kx k 4 : ℝ) - 1 / 16, (I.H : ℝ) - 1 / 4) ((I.kx k 4 : ℝ) + (I.ε : ℝ) / 8, (I.H : ℝ)) := by
    simp only [det]; have := hg.eps_real.1; nlinarith
  rw [r2] at hx
  exact cone4_iff.1 (sees_subset_cone' hP hL hi h2 h1 h3 hconv hx)

/-- **The visibility set of the slope-2 tip lies in the corridor.** -/
theorem Good.sees_tip2_mem {x : Point} (hx : P.Sees x (ratPoint (I.slotTip k 2))) :
    x ∈ I.poly.filled := by
  obtain ⟨i, hi, h1, h2, h3⟩ := hg.tip2_vtx hP hL hC hk
  obtain ⟨r1, r2, r3⟩ := slot2_ratPoint (I := I) k
  have he := hg.eps_real
  obtain ⟨kl, ku⟩ := hg.kx2_real hk
  have hρ := hg.rhoR_pos
  have hρ1 := hg.rhoR_small
  have hconv : 0 < det (ratPoint (I.kx k 2 - I.ε / 8, I.H)) (ratPoint (I.slotTip k 2))
      (ratPoint (I.kx k 2, I.H)) := by
    rw [r1, r2, r3, det_tip2_left]; simp only; nlinarith
  have hmem : ratPoint (I.slotTip k 2) ∈ I.poly.filled := by
    apply mem_poly_of_mem
    obtain ⟨B₁, B₂, hB⟩ := chainBefore_infix_slot2 hk
    rw [hB]; simp [slot2]
  refine Polygon.sees_mem_room hP hL hi h2 h1 h3 hconv (hg.corridor_isRoom hP hL hC) hmem ?_
    (Polygon.sees_comm.1 hx)
  -- the cone misses the doors
  intro y hy hyc
  rw [r1, r2, r3] at hyc
  have hc := cone2_iff.1 hyc
  rcases hy with hyw | hye
  · rw [window, ratPoint_c1', ratPoint_d1'] at hyw
    have hy1 : y.1 = (I.S : ℝ) + 2 := by rw [seg_fst_of_vertical hyw rfl]
    have hy2 : (I.H : ℝ) ≤ y.2 := Vis.Cert.seg_snd_lb hyw (by simp) (by simp; linarith)
    have hy3 : y.2 ≤ (I.H : ℝ) + I.rhoR := Vis.Cert.seg_snd_ub hyw (by simp; linarith) (by simp)
    rw [hy1] at hc
    nlinarith [hc.2]
  · rw [entrance, ratPoint_d0', ratPoint_c0'] at hye
    have hy1 : y.1 = (I.S : ℝ) := by rw [seg_fst_of_vertical hye rfl]
    have hy2 : (I.H : ℝ) ≤ y.2 := Vis.Cert.seg_snd_lb hye (by simp; linarith) (by simp)
    have hy3 : y.2 ≤ (I.H : ℝ) + 2 * I.rhoR :=
      Vis.Cert.seg_snd_ub hye (by simp) (by simp; linarith)
    rw [hy1] at hc
    nlinarith [hc.1]

/-- **The visibility set of the slope-4 tip lies in the corridor.** -/
theorem Good.sees_tip4_mem {x : Point} (hx : P.Sees x (ratPoint (I.slotTip k 4))) :
    x ∈ I.poly.filled := by
  obtain ⟨i, hi, h1, h2, h3⟩ := hg.tip4_vtx hP hL hC hk
  obtain ⟨r1, r2, r3⟩ := slot4_ratPoint (I := I) k
  have he := hg.eps_real
  obtain ⟨kl, ku⟩ := hg.kx4_real hk
  have hρ := hg.rhoR_pos
  have hρ1 := hg.rhoR_small
  have hconv : 0 < det (ratPoint (I.kx k 4, I.H)) (ratPoint (I.slotTip k 4))
      (ratPoint (I.kx k 4 + I.ε / 8, I.H)) := by
    rw [r1, r2, r3]; simp only [det]; nlinarith
  have hmem : ratPoint (I.slotTip k 4) ∈ I.poly.filled := by
    apply mem_poly_of_mem
    obtain ⟨B₁, B₂, hB⟩ := chainBefore_infix_slot4 hk
    rw [hB]; simp [slot4]
  refine Polygon.sees_mem_room hP hL hi h2 h1 h3 hconv (hg.corridor_isRoom hP hL hC) hmem ?_
    (Polygon.sees_comm.1 hx)
  intro y hy hyc
  rw [r1, r2, r3] at hyc
  have hc := cone4_iff.1 hyc
  rcases hy with hyw | hye
  · rw [window, ratPoint_c1', ratPoint_d1'] at hyw
    have hy1 : y.1 = (I.S : ℝ) + 2 := by rw [seg_fst_of_vertical hyw rfl]
    have hy2 : (I.H : ℝ) ≤ y.2 := Vis.Cert.seg_snd_lb hyw (by simp) (by simp; linarith)
    have hy3 : y.2 ≤ (I.H : ℝ) + I.rhoR := Vis.Cert.seg_snd_ub hyw (by simp; linarith) (by simp)
    rw [hy1] at hc
    nlinarith [hc.2]
  · rw [entrance, ratPoint_d0', ratPoint_c0'] at hye
    have hy1 : y.1 = (I.S : ℝ) := by rw [seg_fst_of_vertical hye rfl]
    have hy2 : (I.H : ℝ) ≤ y.2 := Vis.Cert.seg_snd_lb hye (by simp; linarith) (by simp)
    have hy3 : y.2 ≤ (I.H : ℝ) + 2 * I.rhoR :=
      Vis.Cert.seg_snd_ub hye (by simp) (by simp; linarith)
    rw [hy1] at hc
    nlinarith [hc.1]

end Tips

/-! ## Separation of the witnesses -/

section Sep

variable (hg : I.Good N) {P : Polygon} {a b : ℕ} (hP : P.Simple) (hL : P.InteriorLeft)
  (hC : CorridorAt P I a b)
include hg hP hL hC

omit hP hL hC in
/-- Heights of the stationary guards over the floor are in `[1/2, 3/2]`. -/
theorem Good.sgPt_height {j : ℕ} (hj : j < I.np) :
    1 / 2 ≤ ((I.sgPt j).2 : ℝ) - I.H ∧ ((I.sgPt j).2 : ℝ) - I.H ≤ 3 / 2 := by
  have := (hg.sgConfig hj).hh1
  have := (hg.sgConfig hj).hh2
  constructor
  · have h : (1 / 2 : ℚ) ≤ (I.sgPt j).2 - I.H := by linarith
    have := rat_cast_le_of h; push_cast at this; linarith
  · have h : (I.sgPt j).2 - I.H ≤ (3 / 2 : ℚ) := by linarith
    have := rat_cast_le_of h; push_cast at this; linarith

/-- **Other stationary guards do not see the slope-2 tip of pair `k`.** -/
theorem Good.not_sees_tip2_sg {j k : ℕ} (hjk : j ≠ k) (hj : j < I.np) (hk : k < I.np) :
    ¬ P.Sees (ratPoint (I.sgPt j)) (ratPoint (I.slotTip k 2)) := by
  intro hs
  have hc := hg.sees_tip2_cone hP hL hC hk hs
  simp only [ratPoint_fst, ratPoint_snd] at hc
  rw [sgPt_on_slot2 j] at hc
  obtain ⟨h1, h2⟩ := hg.sgPt_height hj
  have he := hg.eps_real
  rcases lt_or_gt_of_ne hjk with h | h
  · have := hg.kx_sep (Or.inl rfl) h hk
    have : (I.kx k 2 : ℝ) + 100 * (I.ε : ℝ) ≤ (I.kx j 2 : ℝ) := by exact_mod_cast this
    linarith [hc.2]
  · have := hg.kx_sep (Or.inl rfl) h hj
    have : (I.kx j 2 : ℝ) + 100 * (I.ε : ℝ) ≤ (I.kx k 2 : ℝ) := by exact_mod_cast this
    nlinarith [hc.1]

/-- **Other stationary guards do not see the slope-4 tip of pair `k`.** -/
theorem Good.not_sees_tip4_sg {j k : ℕ} (hjk : j ≠ k) (hj : j < I.np) (hk : k < I.np) :
    ¬ P.Sees (ratPoint (I.sgPt j)) (ratPoint (I.slotTip k 4)) := by
  intro hs
  have hc := hg.sees_tip4_cone hP hL hC hk hs
  simp only [ratPoint_fst, ratPoint_snd] at hc
  rw [sgPt_on_slot4 j] at hc
  obtain ⟨h1, h2⟩ := hg.sgPt_height hj
  have he := hg.eps_real
  rcases lt_or_gt_of_ne hjk with h | h
  · have := hg.kx_sep (Or.inr rfl) h hk
    have : (I.kx k 4 : ℝ) + 100 * (I.ε : ℝ) ≤ (I.kx j 4 : ℝ) := by exact_mod_cast this
    nlinarith [hc.2]
  · have := hg.kx_sep (Or.inr rfl) h hj
    have : (I.kx j 4 : ℝ) + 100 * (I.ε : ℝ) ≤ (I.kx k 4 : ℝ) := by exact_mod_cast this
    linarith [hc.1]

/-- **The slope-4 witnesses of different pairs have disjoint visibility sets.** -/
theorem Good.not_sees_tip4_tip4 {j k : ℕ} (hjk : j ≠ k) (hj : j < I.np) (hk : k < I.np)
    {x : Point} (hxk : P.Sees x (ratPoint (I.slotTip k 4))) :
    ¬ P.Sees x (ratPoint (I.slotTip j 4)) := by
  intro hxj
  have ck := hg.sees_tip4_cone hP hL hC hk hxk
  have cj := hg.sees_tip4_cone hP hL hC hj hxj
  have hbox := hg.poly_filled_box (hg.sees_tip4_mem hP hL hC hk hxk)
  obtain ⟨-, -, hy1, hy2⟩ := hbox
  have he := hg.eps_real
  rcases lt_or_gt_of_ne hjk with h | h
  · have := hg.kx_sep (Or.inr rfl) h hk
    have : (I.kx k 4 : ℝ) + 100 * (I.ε : ℝ) ≤ (I.kx j 4 : ℝ) := by exact_mod_cast this
    nlinarith [ck.2, cj.1]
  · have := hg.kx_sep (Or.inr rfl) h hj
    have : (I.kx j 4 : ℝ) + 100 * (I.ε : ℝ) ≤ (I.kx k 4 : ℝ) := by exact_mod_cast this
    nlinarith [cj.2, ck.1]

end Sep

end Input

end ArtGallery.Sec5.Corridor

end
