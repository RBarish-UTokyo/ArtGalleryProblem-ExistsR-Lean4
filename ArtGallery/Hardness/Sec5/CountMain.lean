module

public import ArtGallery.Hardness.Sec5.CountAbstract
public import ArtGallery.Hardness.Sec5.MainArea.Steep
public import ArtGallery.Stade.Counting

/-!
# Section 5, counting: the base positions (main area)

The guard segments `s_σ` (`σ < 4n`) of the main area, in a polygon `P` that contains the pockets
of all slots as vertex chains (`MainHyp`).  Main witness `t1`, witnesses `t0, t1, u0, u1` (and
`q1, q2` for a slot with `one` spikes), position `s_σ` (the point `g1 = a_σ + (1/2, 0)` with
spikes).  All positions have rank `0`: the (W3) conditions hold in the strong form
(`sees_t1_other_not_sees`).  The region of the zone is the strip `X_L < x < S`: the pocket rooms
and the steep cones of the shaft witnesses (below the top `y = S + 3N` of the polygon).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.Sec5.Count

open ArtGallery Set Polygon

/-- The base segment `s_σ = [a_σ, a_σ + (3/2, 0)]`. -/
def baseSeg (σ : ℕ) : Set Point :=
  {p | p.2 = 0 ∧ (slotX σ : ℝ) ≤ p.1 ∧ p.1 ≤ slotX σ + 3 / 2}

/-- The region of the main area: `54n − 12 − S < x < S`. -/
def mainReg (n k : ℕ) : Set Point :=
  {p | 54 * (n : ℝ) - 12 - (S n k : ℝ) < p.1 ∧ p.1 < (S n k : ℝ)}

/-- The base positions. -/
noncomputable def mainSys (n : ℕ) (one : ℕ → Bool) : PosSys (Fin (4 * n)) where
  m σ := t1Pt σ
  W σ := {t0Pt σ, t1Pt σ, u0Pt σ, u1Pt σ} ∪ {p | one σ = true ∧ (p = q1Pt σ ∨ p = q2Pt σ)}
  Spot σ := if one σ = true then {g1Pt σ} else baseSeg σ
  rank _ := 0

/-- The hypotheses on the main area. -/
structure MainHyp (P : Polygon) (n k : ℕ) (one : ℕ → Bool) (start : ℕ → ℕ) : Prop where
  simple : P.Simple
  ccw : P.InteriorLeft
  pocket : ∀ σ < 4 * n, PocketAt P (one σ) σ (start σ)
  top : ∀ p ∈ P.filled, p.2 ≤ (S n k : ℝ) + 3 * (bigN n k : ℝ)
  one_lt : ∀ σ, one σ = true → σ < n

namespace MainHyp

variable {P : Polygon} {n k : ℕ} {one : ℕ → Bool} {start : ℕ → ℕ}
  (h : MainHyp P n k one start)
include h

theorem params {σ : ℕ} (hσ : σ < 4 * n) :
    0 ≤ (slotX σ : ℝ) ∧ (slotX σ : ℝ) + 2 ≤ 54 * n ∧ 1000 * (bigN n k : ℝ) ≤ (S n k : ℝ) ∧
      54 * (n : ℝ) ≤ 14 * bigN n k := by
  have h1 : (0 : ℝ) ≤ (slotX σ : ℝ) := by
    simp only [slotX]; push_cast; positivity
  have h2 : (slotX σ : ℝ) + 2 ≤ 54 * n := by
    simp only [slotX]; push_cast
    have : (σ : ℝ) + 1 ≤ 4 * n := by exact_mod_cast hσ
    linarith
  have h3 : 1000 * (bigN n k : ℝ) ≤ (S n k : ℝ) := by
    have := S_ge_mul_bigN (n := n) (k := k)
    have : ((100000 * bigN n k : ℕ) : ℝ) ≤ (S n k : ℝ) := by exact_mod_cast this
    push_cast at this
    have : (0 : ℝ) ≤ bigN n k := by positivity
    linarith
  have h4 : 54 * (n : ℝ) ≤ 14 * bigN n k := by
    have := four_n_le_bigN (n := n) (k := k)
    have : ((4 * n : ℕ) : ℝ) ≤ (bigN n k : ℝ) := by exact_mod_cast this
    push_cast at this
    have : (0 : ℝ) ≤ n := by positivity
    linarith
  exact ⟨h1, h2, h3, h4⟩

/-- A point in a pocket room or in a steep cone `|x − a| ≤ 2 + 2(y + 6)/3` above the door lies in the
region of the main area. -/
theorem reg_of {σ : ℕ} (hσ : σ < 4 * n) {p : Point} (hp : p ∈ P.filled)
    (h' : p ∈ (pocketPoly (one σ) σ).filled ∨
      (1 ≤ p.2 ∧ (slotX σ : ℝ) - 2 / 3 * (p.2 + 6) ≤ p.1 ∧
        p.1 ≤ (slotX σ : ℝ) + 2 + 2 / 3 * (p.2 + 6))) :
    p ∈ mainReg n k := by
  obtain ⟨a1, a2, a3, a4⟩ := h.params hσ
  have hy := h.top p hp
  have hN : (2 : ℝ) ≤ bigN n k := by exact_mod_cast two_le_bigN (n := n) (k := k)
  rcases h' with hr | ⟨b1, b2, b3⟩
  · obtain ⟨c1, c2, -⟩ := pocketPoly_bounds (one σ) σ hr
    exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩

/-- **The visibility sets of the base witnesses lie in the main region.** -/
theorem reg {σ : ℕ} (hσ : σ < 4 * n) {w : Point} (hw : w ∈ (mainSys n one).W ⟨σ, hσ⟩) {p : Point}
    (hs : P.Sees p w) : p ∈ mainReg n k := by
  have hK := h.pocket σ hσ
  have hP := h.simple
  have hL := h.ccw
  have hpf : p ∈ P.filled := hs (Geometry.left_mem_segment p w)
  have hs' := Polygon.sees_comm.1 hs
  rcases hw with hw | ⟨hone, hw⟩
  · simp only [mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · obtain ⟨b1, b2, b3, b4⟩ := sees_t0_box hP hL hK hs'
      refine h.reg_of hσ hpf ?_
      rcases le_or_gt 1 p.2 with hy | hy
      · linarith
      · exact Or.inl (sees_t0_mem_room hP hL hK hs')
    · exact h.reg_of hσ hpf (Or.inl (sees_t1_mem_room hP hL hK hs'))
    · rcases sees_u0_steep hP hL hK hs' with hr | ⟨c1, c2, c3⟩
      · exact h.reg_of hσ hpf (Or.inl hr)
      · exact h.reg_of hσ hpf (Or.inr ⟨c1, by linarith, by linarith⟩)
    · rcases sees_u1_steep hP hL hK hs' with hr | ⟨c1, c2, c3⟩
      · exact h.reg_of hσ hpf (Or.inl hr)
      · exact h.reg_of hσ hpf (Or.inr ⟨c1, by linarith, by linarith⟩)
  · have hK' : PocketAt P true σ (start σ) := hone ▸ hK
    rcases hw with rfl | rfl
    · rcases sees_q1_steep hP hL hK' hs' with hr | ⟨c1, c2, c3⟩
      · exact h.reg_of hσ hpf (Or.inl (hone ▸ hr))
      · exact h.reg_of hσ hpf (Or.inr ⟨c1, by linarith, by linarith⟩)
    · rcases sees_q2_steep hP hL hK' hs' with hr | ⟨c1, c2, c3⟩
      · exact h.reg_of hσ hpf (Or.inl (hone ▸ hr))
      · exact h.reg_of hσ hpf (Or.inr ⟨c1, by linarith, by linarith⟩)

theorem wit_mem_filled {σ : ℕ} (hσ : σ < 4 * n) {w : Point}
    (hw : w ∈ (mainSys n one).W ⟨σ, hσ⟩) : w ∈ P.filled := by
  have hK := h.pocket σ hσ
  have hP := h.simple
  rcases hw with hw | ⟨hone, hw⟩
  · simp only [mem_insert_iff, mem_singleton_iff] at hw
    generalize one σ = b at hK
    rcases hw with rfl | rfl | rfl | rfl <;> cases b
    · exact hK.vtx_mem_filled hP (j := 2) (by decide)
    · exact hK.vtx_mem_filled hP (j := 2) (by decide)
    · exact hK.vtx_mem_filled hP (j := 11) (by decide)
    · exact hK.vtx_mem_filled hP (j := 16) (by decide)
    · exact hK.vtx_mem_filled hP (j := 6) (by decide)
    · exact hK.vtx_mem_filled hP (j := 9) (by decide)
    · exact hK.vtx_mem_filled hP (j := 7) (by decide)
    · exact hK.vtx_mem_filled hP (j := 12) (by decide)
  · have hK' : PocketAt P true σ (start σ) := hone ▸ hK
    rcases hw with rfl | rfl
    · exact hK'.vtx_mem_filled hP (j := 7) (by decide)
    · exact hK'.vtx_mem_filled hP (j := 10) (by decide)

/-- **The base positions satisfy the counting conditions.** -/
theorem ok : (mainSys n one).OK P (mainReg n k) := by
  have hP := h.simple
  have hL := h.ccw
  refine ⟨fun σ => Or.inl (by simp [mainSys]), fun σ w hw => h.wit_mem_filled σ.2 hw,
    fun σ w hw p hs => h.reg σ.2 hw hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- spot
    rintro ⟨σ, hσ⟩ p hp hall
    have hK := h.pocket σ hσ
    have h0 := hall (t0Pt σ) (Or.inl (by simp))
    have h1 := hall (t1Pt σ) (Or.inl (by simp))
    have h2 := hall (u0Pt σ) (Or.inl (by simp))
    have h3 := hall (u1Pt σ) (Or.inl (by simp))
    simp only [mainSys]
    by_cases hone : one σ = true
    · simp only [hone, ↓reduceIte]
      have hK' : PocketAt P true σ (start σ) := hone ▸ hK
      exact guard_segment_one hP hL hK' h0 h1 h2 h3 (hall _ (Or.inr ⟨hone, Or.inl rfl⟩))
        (hall _ (Or.inr ⟨hone, Or.inr rfl⟩))
    · simp only [hone, Bool.false_eq_true, ↓reduceIte]
      exact guard_segment hP hL hK h0 h1 h2 h3
  · -- spot_reg
    rintro ⟨σ, hσ⟩ p hp
    obtain ⟨a1, a2, a3, a4⟩ := h.params (k := k) hσ
    have hN : (2 : ℝ) ≤ bigN n k := by exact_mod_cast two_le_bigN (n := n) (k := k)
    simp only [mainSys] at hp
    split_ifs at hp with hone
    · rcases hp with rfl
      rw [g1Pt, absPt_eq]
      simp only [g1Rel]
      exact ⟨by push_cast; linarith, by push_cast; linarith⟩
    · obtain ⟨-, b1, b2⟩ := hp
      exact ⟨by linarith, by linarith⟩
  · -- spot_disj
    rintro ⟨σ, hσ⟩ ⟨σ', hσ'⟩ hne
    have hss : σ ≠ σ' := fun e => hne (by subst e; rfl)
    have sep := slotX_sep_real hss
    have box : ∀ τ (hτ : τ < 4 * n), ∀ p ∈ (mainSys n one).Spot ⟨τ, hτ⟩,
        (slotX τ : ℝ) ≤ p.1 ∧ p.1 ≤ slotX τ + 3 / 2 := by
      intro τ hτ p hp
      simp only [mainSys] at hp
      split_ifs at hp with hone
      · rcases hp with rfl
        rw [g1Pt, absPt_eq]; simp only [g1Rel]; push_cast
        exact ⟨by linarith, by linarith⟩
      · exact ⟨hp.2.1, hp.2.2⟩
    rw [Set.disjoint_left]
    intro p hp hp'
    have b1 := box σ hσ p hp
    have b2 := box σ' hσ' p hp'
    rcases sep with e | e <;> linarith [b1.1, b1.2, b2.1, b2.2]
  · -- disj
    rintro ⟨σ, hσ⟩ ⟨σ', hσ'⟩ hne p h1 h2
    have hss : σ ≠ σ' := fun e => hne (by subst e; rfl)
    exact not_sees_t1_t1 hP hL (h.pocket σ hσ) (h.pocket σ' hσ') hss h1 h2
  · -- early (all ranks are `0`)
    intro X Y _ hr
    exact absurd hr (lt_irrefl 0)
  · -- late
    rintro ⟨σ, hσ⟩ ⟨σ', hσ'⟩ hne - w hw p h1 h2
    have hss : σ' ≠ σ := fun e => hne (by subst e; rfl)
    have hK := h.pocket σ hσ
    obtain ⟨n0, n1, n2, n3⟩ := sees_t1_other_not_sees hP hL hK (h.pocket σ' hσ') hss h1
    rcases hw with hw | ⟨hone, hw⟩
    · simp only [mem_insert_iff, mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl
      exacts [n0 h2, n1 h2, n2 h2, n3 h2]
    · have hK' : PocketAt P true σ (start σ) := hone ▸ hK
      obtain ⟨m0, m1⟩ := sees_t1_other_not_sees_q hP hL hK' (h.pocket σ' hσ') hss h1
      rcases hw with rfl | rfl
      exacts [m0 h2, m1 h2]

end MainHyp

end ArtGallery.Sec5.Count

end
