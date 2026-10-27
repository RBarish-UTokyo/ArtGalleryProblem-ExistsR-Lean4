module

public import ArtGallery.Hardness.Sec5.Cover
public import ArtGallery.Hardness.Sec5.ConstraintGlobal
public import ArtGallery.Hardness.Sec5.Assemble

/-!
# Section 5: Theorem 54

Assembly of the reduction from ETR-INV to the art gallery problem.  To have `n ≥ 1` available
for the global construction, we use the polygon of `Φ` with `N = max n 1` variables (for `n = 0`
the instance `Φ` is empty, and the polygon is the one of the empty instance on one variable).

* `polyC Φ N` is simple (`construct_simple`);
* every guard set has at least `numGuards Φ N` guards (`Count.count_lower`);
* a guard set with `numGuards Φ N` guards encodes a solution (`Constraint.guardSet_solution`);
* a solution gives a guard set with `numGuards Φ N` guards (`canonGuards`);
* a guard set with `numGuards Φ N` guards contains a unique guard on each base segment
  `s_i` (`base_guard_unique`), which fixes the values `x_i` (`i < n`).
-/

@[expose] public section

namespace ArtGallery.Sec5

open ArtGallery Set Polygon ArtGallery.Sec5.Count

/-- The bound on the variable indices is monotone. -/
theorem varsLt_mono {c : ETRINV.Constraint} {n N : ℕ} (h : n ≤ N) (hc : c.VarsLt n) :
    c.VarsLt N := by
  cases c <;> simp only [ETRINV.Constraint.VarsLt] at hc ⊢ <;> omega

/-- A constraint only depends on the values of its variables. -/
theorem holds_congr {c : ETRINV.Constraint} {n : ℕ} (hc : c.VarsLt n) {x y : ℕ → ℝ}
    (hxy : ∀ i < n, x i = y i) (h : c.Holds x) : c.Holds y := by
  cases c with
  | one a =>
    simp only [ETRINV.Constraint.VarsLt] at hc
    simp only [ETRINV.Constraint.Holds] at h ⊢
    rw [← hxy a hc]; exact h
  | add a b d =>
    simp only [ETRINV.Constraint.VarsLt] at hc
    simp only [ETRINV.Constraint.Holds] at h ⊢
    rw [← hxy a hc.1, ← hxy b hc.2.1, ← hxy d hc.2.2]; exact h
  | inv a b =>
    simp only [ETRINV.Constraint.VarsLt] at hc
    simp only [ETRINV.Constraint.Holds] at h ⊢
    rw [← hxy a hc.1, ← hxy b hc.2]; exact h

/-- The base segments of distinct slots are disjoint. -/
theorem baseSeg_disjoint {σ τ : ℕ} (h : σ ≠ τ) : Disjoint (baseSeg σ) (baseSeg τ) := by
  rw [Set.disjoint_left]
  rintro p ⟨-, h1, h2⟩ ⟨-, h3, h4⟩
  simp only [slotX] at h1 h2 h3 h4
  push_cast at h1 h2 h3 h4
  rcases lt_or_gt_of_ne h with h' | h'
  · have : (σ : ℝ) + 1 ≤ τ := by exact_mod_cast h'
    linarith
  · have : (τ : ℝ) + 1 ≤ σ := by exact_mod_cast h'
    linarith

/-- The base segment of a slot lies in the region of the main area. -/
theorem baseSeg_mainReg {Φ : List ETRINV.Constraint} {n σ : ℕ} (hσ : σ < 4 * n) :
    baseSeg σ ⊆ gReg Φ n (.inl ()) := by
  rintro p ⟨-, h1, h2⟩
  have hS := S_big (n := n) (Φ := Φ)
  have hσ' : (σ : ℝ) + 1 ≤ 4 * n := by exact_mod_cast hσ
  have h0 : (0 : ℝ) ≤ σ := by positivity
  simp only [slotX] at h1 h2
  push_cast at h1 h2
  simp only [gReg, mainReg, Set.mem_ofPred_eq]
  constructor <;> linarith

/-- The position of a base slot lies on its base segment. -/
theorem gPosSpot_main_sub {Φ : List ETRINV.Constraint} {n : ℕ} (σ : Fin (4 * n)) :
    gPosSpot (⟨.inl (), σ⟩ : GPos Φ n) ⊆ baseSeg σ := by
  rw [gPosSpot_main]
  split_ifs
  · rintro p rfl
    simp only [g1Pt, absPt_eq, g1Rel, baseSeg, Set.mem_ofPred_eq]
    norm_num
  · exact le_rfl

/-- **The guard on a base segment is unique**: in a guard set with `numGuards Φ n` guards, a
guard on the base segment `s_σ` is the guard of the base position `σ`. -/
theorem base_guard_unique {Φ : List ETRINV.Constraint} {n : ℕ} (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    (hn : 0 < n) {G : Finset Point} (e : GPos Φ n ≃ G)
    (he : ∀ X, (e X : Point) ∈ gPosSpot X ∧ ∀ q ∈ G, q ∈ gPosSpot X → q = e X)
    (σ : Fin (4 * n)) {p : Point} (hpG : p ∈ G) (hp : p ∈ baseSeg σ) :
    p = e ⟨.inl (), σ⟩ := by
  obtain ⟨⟨z, Y⟩, hY⟩ := e.surjective ⟨p, hpG⟩
  have hpY : p ∈ gPosSpot (⟨z, Y⟩ : GPos Φ n) := by
    have := (he ⟨z, Y⟩).1
    rwa [hY] at this
  rcases z with _ | j | j
  · change Fin (4 * n) at Y
    by_cases hYσ : Y = σ
    · subst hYσ
      rw [hY]
    · exfalso
      have hne : (Y : ℕ) ≠ σ := fun h => hYσ (Fin.ext h)
      exact Set.disjoint_left.1 (baseSeg_disjoint hne) (gPosSpot_main_sub Y hpY) hp
  · exfalso
    have h1 := (gZ_ok hΦ hn (.inr (.inl j))).spot_reg Y hpY
    have h2 := baseSeg_mainReg (Φ := Φ) σ.2 hp
    exact Set.disjoint_left.1 (gReg_disjoint _ _ (by simp)) h2 h1
  · exfalso
    have h1 := (gZ_ok hΦ hn (.inr (.inr j))).spot_reg Y hpY
    have h2 := baseSeg_mainReg (Φ := Φ) σ.2 hp
    exact Set.disjoint_left.1 (gReg_disjoint _ _ (by simp)) h2 h1

/-- The representative guard `(x_i + d_i, 0)` of a value `x_i ∈ [1/2, 2]` lies on the base
segment `s_i`. -/
theorem shift_mem_baseSeg {i : ℕ} {v : ℝ} (hv : 1 / 2 ≤ v ∧ v ≤ 2) :
    (v + ((shift i : ℚ) : ℝ), (0 : ℝ)) ∈ baseSeg i := by
  refine ⟨rfl, ?_, ?_⟩ <;> simp only [slotX, shift] <;> push_cast <;> linarith [hv.1, hv.2]

/-- **Theorem 54** (Section 5 form): the polygon `polyC Φ (max n 1)`, the number
`numGuards Φ (max n 1)` and the shifts `d_i = 27i/2 − 1/2`. -/
theorem etrinv_guard_correspondence' (Φ : List ETRINV.Constraint) (n : ℕ)
    (hΦ : ∀ c ∈ Φ, c.VarsLt n) :
    ∃ (V : List (ℚ × ℚ)) (g : ℕ) (d : ℕ → ℚ),
      (Polygon.mk (V.map ratPoint)).Simple ∧
      (∀ G : Finset Point, (Polygon.mk (V.map ratPoint)).IsGuardSet (G : Set Point) →
        g ≤ G.card) ∧
      (∀ G : Finset Point, (Polygon.mk (V.map ratPoint)).IsGuardSet (G : Set Point) →
        G.card = g → ∃ x : ℕ → ℝ, ((∀ i < n, 1 / 2 ≤ x i ∧ x i ≤ 2) ∧ ∀ c ∈ Φ, c.Holds x) ∧
          ∀ i < n, (x i + (d i : ℝ), (0 : ℝ)) ∈ G) ∧
      ∀ x : ℕ → ℝ,
        ((∀ i < n, 1 / 2 ≤ x i ∧ x i ≤ 2) ∧ ∀ c ∈ Φ, c.Holds x) ↔
          (∀ i < n, 1 / 2 ≤ x i ∧ x i ≤ 2) ∧ ∃ G : Finset Point, G.card = g ∧
            (Polygon.mk (V.map ratPoint)).IsGuardSet (G : Set Point) ∧
            ∀ i < n, (x i + (d i : ℝ), (0 : ℝ)) ∈ G := by
  set N := max n 1 with hNdef
  have hnN : n ≤ N := le_max_left _ _
  have hN : 0 < N := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hΦN : ∀ c ∈ Φ, c.VarsLt N := fun c hc => varsLt_mono hnN (hΦ c hc)
  refine ⟨construct Φ N, numGuards Φ N, shift, (construct_simple hΦN).1,
    fun G hG => Count.count_lower hΦN G hG, ?_, ?_⟩
  · intro G hG hcard
    obtain ⟨y, hy, hΦy, hyG⟩ := Constraint.guardSet_solution hΦN hN G hG hcard
    exact ⟨y, ⟨fun i hi => hy i (by omega), hΦy⟩, fun i hi => hyG i (by omega)⟩
  · intro x
    constructor
    · rintro ⟨hx, hΦx⟩
      refine ⟨hx, ?_⟩
      -- extend `x` by the value `1` beyond `n`
      set x' : ℕ → ℝ := fun i => if i < n then x i else 1 with hx'def
      have hxx' : ∀ i < n, x i = x' i := fun i hi => by simp [hx'def, hi]
      have hx' : ∀ i < N, 1 / 2 ≤ x' i ∧ x' i ≤ 2 := by
        intro i _
        by_cases hi : i < n
        · rw [← hxx' i hi]; exact hx i hi
        · simp only [hx'def, hi, ite_false]; norm_num
      have hΦx' : ∀ c ∈ Φ, c.Holds x' := fun c hc => holds_congr (hΦ c hc) hxx' (hΦx c hc)
      refine ⟨canonGuards Φ N x', canonGuards_card hΦN hx' hΦx',
        canonGuards_guard hΦN hN hx' hΦx', fun i hi => ?_⟩
      rw [hxx' i hi]
      exact canonGuards_mem i (by omega)
    · rintro ⟨hx, G, hcard, hG, hxG⟩
      refine ⟨hx, ?_⟩
      obtain ⟨y, hy, hΦy, hyG⟩ := Constraint.guardSet_solution hΦN hN G hG hcard
      obtain ⟨e, he⟩ := Count.count_pinned hΦN hN G hG hcard
      have hyx : ∀ i < n, y i = x i := by
        intro i hi
        have h1 := base_guard_unique hΦN hN e he ⟨i, by omega⟩ (hxG i hi)
          (shift_mem_baseSeg (hx i hi))
        have h2 := base_guard_unique hΦN hN e he ⟨i, by omega⟩ (hyG i (by omega))
          (shift_mem_baseSeg (hy i (by omega)))
        have := congrArg Prod.fst (h2.trans h1.symm)
        simp only at this
        linarith
      exact fun c hc => holds_congr (hΦ c hc) hyx (hΦy c hc)

end ArtGallery.Sec5

end
