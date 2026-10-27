module

public import ArtGallery.Hardness.BP.MainAreaRoom
public import ArtGallery.Hardness.Sec5.Assemble.Bottom

/-!
# Boundary-point variant: the bottom wall with bays is a simple chain

The bottom wall `w_l, pockets 0 … 4n−1, w_r` (`bottomWallBP n Φ ++ [w_r]`) is a simple chain lying
in `[−6, 54n − 6] × (−∞, 1]` (`bottomBP_chain`), as in Section 5 (`Sec5/Assemble/Bottom.lean`):
pocket `σ` with its right mouth corner is the simple chain `pocketBPClosed σ` (a prefix of the
simple room polygon, `simple_pocketPolyBP`) from `m_L(σ) = (27σ/2 − 6, 1)` to
`m_R(σ) = (27σ/2 + 15/2, 1)`; its inner vertices (the bay) lie strictly between the vertical lines
through these two corners; consecutive pockets share the corner `m_R(σ) = m_L(σ + 1)`.
-/

@[expose] public section

namespace ArtGallery.BP

open ArtGallery Set
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue
open ArtGallery.Sec5 (Q2 slotX slotA slotOne mouthL mouthR mL mR wR slotX_succ slotX_nonneg
  ratPoint_mL ratPoint_mR mL_succ mR_last)

/-- The bay vertices lie strictly between the mouth corners' verticals, below `y = 1`. -/
theorem bayRel_bounds (one : Bool) :
    ∀ v ∈ bayRel one, -6 < v.1 ∧ v.1 < 15 / 2 ∧ v.2 ≤ 1 := by
  cases one <;> decide +kernel

theorem pocketBP_eq (one : Bool) (σ : ℕ) :
    pocketBP one σ = mL σ :: (bayRel one).map (· + slotA σ) := by
  rw [pocketBP, pocketBPRel]; rfl

/-- The absolute bay vertices of slot `σ` (real). -/
noncomputable def innerRBP (one : Bool) (σ : ℕ) : List Point :=
  ((bayRel one).map (· + slotA σ)).map ratPoint

theorem innerRBP_bounds (one : Bool) (σ : ℕ) : ∀ v ∈ innerRBP one σ,
    (slotX σ : ℝ) - 6 < v.1 ∧ v.1 < (slotX σ : ℝ) + 15 / 2 ∧ v.2 ≤ 1 := by
  intro v hv
  simp only [innerRBP, List.map_map, List.mem_map, Function.comp] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  obtain ⟨h1, h2, h3⟩ := bayRel_bounds one w hw
  have h1' : ((-6 : ℚ) : ℝ) < (w.1 : ℝ) := by exact_mod_cast h1
  have h2' : (w.1 : ℝ) < ((15 / 2 : ℚ) : ℝ) := by exact_mod_cast h2
  have h3' : (w.2 : ℝ) ≤ ((1 : ℚ) : ℝ) := by exact_mod_cast h3
  push_cast at h1' h2' h3'
  simp only [ratPoint, slotA, Prod.fst_add, Prod.snd_add, add_zero]
  push_cast
  refine ⟨by linarith, by linarith, h3'⟩

theorem innerRBP_ne_nil (one : Bool) (σ : ℕ) : innerRBP one σ ≠ [] := by
  cases one <;> simp [innerRBP, bayRel, bayL]

/-- The closed pocket chain in real coordinates. -/
theorem pocketBPClosed_map (one : Bool) (σ : ℕ) : (pocketBPClosed one σ).map ratPoint =
    ratPoint (mL σ) :: innerRBP one σ ++ [ratPoint (mR σ)] := by
  rw [pocketBPClosed_eq, pocketBP_eq]
  simp [innerRBP]

/-- **A pocket with its bay is a simple chain.** -/
theorem pocketBP_chainSimple (one : Bool) (σ : ℕ) :
    ChainSimple (ratPoint (mL σ) :: innerRBP one σ ++ [ratPoint (mR σ)]) := by
  rw [← pocketBPClosed_map]
  have h := simple_pocketPolyBP one σ
  rw [pocketPolyBP, ← List.append_nil ((pocketBPClosed one σ).map ratPoint)] at h
  exact chainSimple_of_simple h

theorem slotX_cast_succ_BP (σ : ℕ) : (slotX (σ + 1) : ℝ) = (slotX σ : ℝ) + 27 / 2 := by
  rw [slotX_succ]; push_cast; ring

/-- **Prefixes of the bottom wall.**  The pockets `0 … j` followed by `m_R(j)` form a simple chain
in `[−6, 27j/2 + 15/2] × (−∞, 1]` reaching `x = 27j/2 + 15/2` only at `m_R(j)`. -/
theorem bottomBP_prefix (one : ℕ → Bool) : ∀ j : ℕ,
    ChainSimple (((List.range (j + 1)).flatMap fun σ => pocketBP (one σ) σ).map ratPoint ++
        [ratPoint (mR j)]) ∧
      (∀ p ∈ chainSet (((List.range (j + 1)).flatMap fun σ => pocketBP (one σ) σ).map ratPoint ++
        [ratPoint (mR j)]), -6 ≤ p.1 ∧ p.1 ≤ (slotX j : ℝ) + 15 / 2 ∧ p.2 ≤ 1 ∧
          ((slotX j : ℝ) + 15 / 2 ≤ p.1 → p = ratPoint (mR j)))
  | 0 => by
    have e : ((List.range (0 + 1)).flatMap fun σ => pocketBP (one σ) σ).map ratPoint ++
        [ratPoint (mR 0)] = ratPoint (mL 0) :: innerRBP (one 0) 0 ++ [ratPoint (mR 0)] := by
      rw [← pocketBPClosed_map, pocketBPClosed_eq]; simp
    rw [e]
    have hb := innerRBP_bounds (one 0) 0
    have h0 : (slotX 0 : ℝ) = 0 := by simp [slotX]
    refine ⟨pocketBP_chainSimple _ _, fun p hp => ⟨?_, ?_, ?_, fun hx => ?_⟩⟩
    · have := chainSet_subset_halfplane (α := -1) (β := 0) (c := 6) (l := _) (fun v hv => by
        simp only [List.cons_append, List.mem_cons, List.mem_append,
          List.not_mem_nil, or_false] at hv
        rcases hv with rfl | hv | rfl
        · rw [ratPoint_mL]; simp [h0]
        · have := (hb v hv).1; rw [h0] at this; linarith
        · rw [ratPoint_mR]; simp [h0]; norm_num) p hp
      linarith
    · have := chainSet_subset_halfplane (α := 1) (β := 0) (c := (slotX 0 : ℝ) + 15 / 2) (l := _)
        (fun v hv => by
        simp only [List.cons_append, List.mem_cons, List.mem_append,
          List.not_mem_nil, or_false] at hv
        rcases hv with rfl | hv | rfl
        · rw [ratPoint_mL]; simp; linarith
        · have := (hb v hv).2.1; linarith
        · rw [ratPoint_mR]; simp) p hp
      linarith
    · have := chainSet_subset_halfplane (α := 0) (β := 1) (c := 1) (l := _) (fun v hv => by
        simp only [List.cons_append, List.mem_cons, List.mem_append,
          List.not_mem_nil, or_false] at hv
        rcases hv with rfl | hv | rfl
        · rw [ratPoint_mL]; simp
        · have := (hb v hv).2.2; linarith
        · rw [ratPoint_mR]; simp) p hp
      linarith
    · rcases chainSet_lt_or_ends (α := 1) (β := 0) (c := (slotX 0 : ℝ) + 15 / 2)
        (innerRBP_ne_nil _ _) (by rw [ratPoint_mL]; simp; linarith) (by rw [ratPoint_mR]; simp)
        (fun v hv => by have := (hb v hv).2.1; linarith) p hp with h | h | h
      · linarith
      · rw [h, ratPoint_mL] at hx; simp at hx; linarith
      · exact h
  | j + 1 => by
    obtain ⟨ih1, ih2⟩ := bottomBP_prefix one j
    set A := ((List.range (j + 1)).flatMap fun σ => pocketBP (one σ) σ).map ratPoint
    have hb := innerRBP_bounds (one (j + 1)) (j + 1)
    have hX := slotX_cast_succ_BP j
    have hXq := slotX_succ j
    have hmL : ratPoint (mL (j + 1)) = ratPoint (mR j) := by rw [mL_succ]
    have e : ((List.range (j + 1 + 1)).flatMap fun σ => pocketBP (one σ) σ).map ratPoint ++
        [ratPoint (mR (j + 1))] =
        A ++ ratPoint (mR j) :: (innerRBP (one (j + 1)) (j + 1) ++ [ratPoint (mR (j + 1))]) := by
      rw [List.range_succ, List.flatMap_append, List.map_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [pocketBP_eq, ← hmL]
      simp [A, innerRBP]
    have hP := pocketBP_chainSimple (one (j + 1)) (j + 1)
    rw [hmL] at hP
    -- the new pocket reaches `x ≤ 27j/2 + 15/2` only at its left corner
    have hPl : ∀ p ∈ chainSet (ratPoint (mR j) :: innerRBP (one (j + 1)) (j + 1) ++
        [ratPoint (mR (j + 1))]), p.1 ≤ (slotX j : ℝ) + 15 / 2 → p = ratPoint (mR j) := by
      intro p hp hx
      rcases chainSet_lt_or_ends (α := -1) (β := 0) (c := -((slotX j : ℝ) + 15 / 2))
        (innerRBP_ne_nil _ _) (by rw [ratPoint_mR]; simp) (by rw [ratPoint_mR]; simp; linarith)
        (fun v hv => by have := (hb v hv).1; linarith) p hp with h | h | h
      · linarith
      · exact h
      · rw [h, ratPoint_mR] at hx; simp at hx; linarith
    have hall : ∀ v ∈ ratPoint (mR j) :: innerRBP (one (j + 1)) (j + 1) ++ [ratPoint (mR (j + 1))],
        (slotX j : ℝ) + 15 / 2 ≤ v.1 ∧ v.1 ≤ (slotX (j + 1) : ℝ) + 15 / 2 ∧ v.2 ≤ 1 := by
      intro v hv
      simp only [List.cons_append, List.mem_cons, List.mem_append,
          List.not_mem_nil, or_false] at hv
      rcases hv with rfl | hv | rfl
      · rw [ratPoint_mR]; simp; linarith
      · obtain ⟨a, b, c⟩ := hb v hv; exact ⟨by linarith, by linarith, c⟩
      · rw [ratPoint_mR]; simp; linarith
    have hPb : ∀ p ∈ chainSet (ratPoint (mR j) :: innerRBP (one (j + 1)) (j + 1) ++
        [ratPoint (mR (j + 1))]), (slotX j : ℝ) + 15 / 2 ≤ p.1 ∧
          p.1 ≤ (slotX (j + 1) : ℝ) + 15 / 2 ∧ p.2 ≤ 1 := by
      intro p hp
      refine ⟨?_, ?_, ?_⟩
      · have := chainSet_subset_halfplane (α := -1) (β := 0) (c := -((slotX j : ℝ) + 15 / 2))
          (fun v hv => by have := (hall v hv).1; linarith) p hp
        linarith
      · have := chainSet_subset_halfplane (α := 1) (β := 0) (c := (slotX (j + 1) : ℝ) + 15 / 2)
          (fun v hv => by have := (hall v hv).2.1; linarith) p hp
        linarith
      · have := chainSet_subset_halfplane (α := 0) (β := 1) (c := 1)
          (fun v hv => by have := (hall v hv).2.2; linarith) p hp
        linarith
    have hPr : ∀ p ∈ chainSet (ratPoint (mR j) :: innerRBP (one (j + 1)) (j + 1) ++
        [ratPoint (mR (j + 1))]), (slotX (j + 1) : ℝ) + 15 / 2 ≤ p.1 →
          p = ratPoint (mR (j + 1)) := by
      intro p hp hx
      rcases chainSet_lt_or_ends (α := 1) (β := 0) (c := (slotX (j + 1) : ℝ) + 15 / 2)
        (innerRBP_ne_nil _ _) (by rw [ratPoint_mR]; simp; linarith) (by rw [ratPoint_mR]; simp)
        (fun v hv => by have := (hb v hv).2.1; linarith) p hp with h | h | h
      · linarith
      · rw [h, ratPoint_mR] at hx; simp at hx; linarith
      · exact h
    rw [e]
    refine ⟨ChainSimple.join ih1 (by simpa using hP) ?_, ?_⟩
    · rintro x ⟨hx1, hx2⟩
      have hx2' : x ∈ chainSet (ratPoint (mR j) :: innerRBP (one (j + 1)) (j + 1) ++
          [ratPoint (mR (j + 1))]) := by simpa using hx2
      exact hPl x hx2' (ih2 x hx1).2.1
    · intro p hp
      rw [chainSet_append_cons] at hp
      rcases hp with hp | hp
      · obtain ⟨a, b, c, -⟩ := ih2 p hp
        exact ⟨a, by linarith, c, fun hx => by linarith⟩
      · have hp' : p ∈ chainSet (ratPoint (mR j) :: innerRBP (one (j + 1)) (j + 1) ++
            [ratPoint (mR (j + 1))]) := by simpa using hp
        obtain ⟨a, b, c⟩ := hPb p hp'
        have : (0 : ℝ) ≤ slotX j := by exact_mod_cast slotX_nonneg j
        exact ⟨by linarith, b, c, hPr p hp'⟩

/-- **The bottom wall is a simple chain** from `w_l` to `w_r` in `[−6, 54n − 6] × (−∞, 1]`. -/
theorem bottomBP_chain {n : ℕ} (hn : 0 < n) (Φ : List ETRINV.Constraint) :
    ChainSimple ((bottomWallBP n Φ ++ [wR n]).map ratPoint) ∧
      ∀ p ∈ chainSet ((bottomWallBP n Φ ++ [wR n]).map ratPoint),
        -6 ≤ p.1 ∧ p.1 ≤ 54 * (n : ℝ) - 6 ∧ p.2 ≤ 1 := by
  obtain ⟨j, hj⟩ : ∃ j, 4 * n = j + 1 := ⟨4 * n - 1, by omega⟩
  have e : (bottomWallBP n Φ ++ [wR n]).map ratPoint =
      ((List.range (j + 1)).flatMap fun σ => pocketBP (slotOne n Φ σ) σ).map ratPoint ++
        [ratPoint (mR j)] := by
    rw [List.map_append, bottomWallBP, hj, show j = 4 * n - 1 by omega, mR_last hn]; simp
  have hX : (slotX j : ℝ) + 15 / 2 = 54 * (n : ℝ) - 6 := by
    have : ((j : ℕ) : ℝ) = 4 * (n : ℝ) - 1 := by
      have : ((j + 1 : ℕ) : ℝ) = ((4 * n : ℕ) : ℝ) := by rw [hj]
      push_cast at this; linarith
    simp only [slotX]; push_cast; rw [this]; ring
  obtain ⟨h1, h2⟩ := bottomBP_prefix (slotOne n Φ) j
  rw [e]
  refine ⟨h1, fun p hp => ?_⟩
  obtain ⟨a, b, c, -⟩ := h2 p hp
  exact ⟨a, by linarith, c⟩

theorem bottomBP_fst {n : ℕ} (hn : 0 < n) (Φ : List ETRINV.Constraint) :
    fstPt ((bottomWallBP n Φ ++ [wR n]).map ratPoint) = ((-6 : ℝ), 1) := by
  obtain ⟨j, hj⟩ : ∃ j, 4 * n = j + 1 := ⟨4 * n - 1, by omega⟩
  rw [bottomWallBP, hj, List.range_succ_eq_map]
  simp only [List.flatMap_cons, pocketBP_eq, List.cons_append, List.map_cons]
  rw [fstPt_cons, ratPoint_mL]
  simp [slotX]

end ArtGallery.BP

end
