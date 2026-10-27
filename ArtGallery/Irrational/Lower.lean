module

public import ArtGallery.Irrational.Vertices

/-!
# Guard sets with at most three guards (Lemmas 5, 6 and 9)

Let `G` be a guard set of `𝒫` with at most three guards.

* **Lemma 5** (`three_lines`): the six apexes of the triangular pockets force one guard on each
  of the lines `l_ℓ : x = 2`, `l_m : y = 0.3 x - 1.05` and `l_r : x = 19`, and no other guard.
  A point seeing an apex lies in an explicit region (`see_a1`, …, `see_a6`, by a point of the
  segment outside `U` close to the apex); the regions of apexes of different pockets pairs are
  disjoint inside `U`.
* **Lemma 6**: the top corners of `R_m` force the middle guard to `x ∈ [10.5, 10.6]`; the far
  corners of `R_ℓ` and `R_r` force one of the two other guards to height `[1.7, 1.8]` and the
  other one to `[0.5, 0.6]`.
* **Lemma 9**: the guard on `l_ℓ` is the low one (otherwise the corner `(12, -34/21)` of `P_b^r`
  is unseen).

Result (`guard_ranges`): `G ⊆ {(2, h), (x, 0.3x - 1.05), (19, k)}`, all three in `G`, with
`h ∈ [0.5, 0.6]`, `x ∈ [10.5, 10.6]`, `k ∈ [1.7, 1.8]`.
-/

namespace ArtGallery.Irrational

@[expose] public section

open Set

/-! ### The apexes of the triangular pockets -/

theorem see_a1 {p : Point} (hpU : p ∈ U) (hs : P.Sees p ((2 : ℝ), (-1/2 : ℝ))) : p.1 ≤ 2 := by
  obtain ⟨b1, b2, b3, b4⟩ := U_bounds hpU
  by_contra hc; push Not at hc
  refine not_sees_wit (p := ((2 : ℝ), (-1/2 : ℝ))) (q := p) (t := 1/100) (by norm_num)
    (by norm_num) ?_ (sees_symm hs)
  intro hw; U_cases hw <;> linarith

theorem see_a2 {p : Point} (hpU : p ∈ U) (hs : P.Sees p ((2 : ℝ), (9/2 : ℝ))) :
    2 ≤ p.1 ∧ 5 * p.1 + p.2 ≤ 29 / 2 := by
  obtain ⟨b1, b2, b3, b4⟩ := U_bounds hpU
  constructor
  · by_contra hc; push Not at hc
    refine not_sees_wit (p := ((2 : ℝ), (9/2 : ℝ))) (q := p) (t := 1/100) (by norm_num)
      (by norm_num) ?_ (sees_symm hs)
    intro hw; U_cases hw <;> linarith
  · by_contra hc; push Not at hc
    refine not_sees_wit (p := ((2 : ℝ), (9/2 : ℝ))) (q := p) (t := 1/100) (by norm_num)
      (by norm_num) ?_ (sees_symm hs)
    intro hw; U_cases hw <;> linarith

theorem see_a3 {p : Point} (hpU : p ∈ U) (hs : P.Sees p ((3 : ℝ), (-3/20 : ℝ))) :
    3 ≤ p.1 ∧ 6 * p.1 - 20 * p.2 - 21 ≤ 0 := by
  obtain ⟨b1, b2, b3, b4⟩ := U_bounds hpU
  constructor
  · by_contra hc; push Not at hc
    refine not_sees_wit (p := ((3 : ℝ), (-3/20 : ℝ))) (q := p) (t := 1/100) (by norm_num)
      (by norm_num) ?_ (sees_symm hs)
    intro hw; U_cases hw <;> linarith
  · by_contra hc; push Not at hc
    refine not_sees_wit (p := ((3 : ℝ), (-3/20 : ℝ))) (q := p) (t := 1/100) (by norm_num)
      (by norm_num) ?_ (sees_symm hs)
    intro hw; U_cases hw <;> linarith

theorem see_a4 {p : Point} (hpU : p ∈ U) (hs : P.Sees p ((52/3 : ℝ), (83/20 : ℝ))) :
    p.1 ≤ 52 / 3 ∧ 0 ≤ 6 * p.1 - 20 * p.2 - 21 ∧ 3 ≤ p.1 := by
  obtain ⟨b1, b2, b3, b4⟩ := U_bounds hpU
  have e1 : p.1 ≤ 52 / 3 := by
    by_contra hc; push Not at hc
    refine not_sees_wit (p := ((52/3 : ℝ), (83/20 : ℝ))) (q := p) (t := 1/100) (by norm_num)
      (by norm_num) ?_ (sees_symm hs)
    intro hw; U_cases hw <;> linarith
  have e2 : 0 ≤ 6 * p.1 - 20 * p.2 - 21 := by
    by_contra hc; push Not at hc
    refine not_sees_wit (p := ((52/3 : ℝ), (83/20 : ℝ))) (q := p) (t := 1/100) (by norm_num)
      (by norm_num) ?_ (sees_symm hs)
    intro hw; U_cases hw <;> linarith
  refine ⟨e1, e2, ?_⟩
  by_contra hc; push Not at hc
  have hT : p ∈ hp cTbl := by
    have hpU' := hpU
    U_cases hpU' <;> first | (exfalso; linarith) | (piece_goal <;> linarith)
  piece_simp at hT
  casesm* _ ∧ _
  refine not_sees_wit (p := p) (q := ((52/3 : ℝ), (83/20 : ℝ))) (t := 1/30) (by norm_num)
    (by norm_num) ?_ hs
  intro hw; U_cases hw <;> linarith

theorem see_a5 {p : Point} (hpU : p ∈ U) (hs : P.Sees p ((19 : ℝ), (-1/2 : ℝ))) :
    p.1 ≤ 19 ∧ 189 ≤ 10 * p.1 + 2 * p.2 := by
  obtain ⟨b1, b2, b3, b4⟩ := U_bounds hpU
  constructor
  · by_contra hc; push Not at hc
    refine not_sees_wit (p := ((19 : ℝ), (-1/2 : ℝ))) (q := p) (t := 1/100) (by norm_num)
      (by norm_num) ?_ (sees_symm hs)
    intro hw; U_cases hw <;> linarith
  · by_contra hc; push Not at hc
    refine not_sees_wit (p := ((19 : ℝ), (-1/2 : ℝ))) (q := p) (t := 1/100) (by norm_num)
      (by norm_num) ?_ (sees_symm hs)
    intro hw; U_cases hw <;> linarith

theorem see_a6 {p : Point} (hpU : p ∈ U) (hs : P.Sees p ((19 : ℝ), (9/2 : ℝ))) : 19 ≤ p.1 := by
  obtain ⟨b1, b2, b3, b4⟩ := U_bounds hpU
  by_contra hc; push Not at hc
  refine not_sees_wit (p := ((19 : ℝ), (9/2 : ℝ))) (q := p) (t := 1/100) (by norm_num)
    (by norm_num) ?_ (sees_symm hs)
  intro hw; U_cases hw <;> linarith

/-- The regions of the apexes of `T_b^m` and `T_b^r` are disjoint inside `U`. -/
theorem excl35 {p : Point} (hpU : p ∈ U) (h1 : 3 ≤ p.1) (h2 : 6 * p.1 - 20 * p.2 - 21 ≤ 0)
    (h3 : p.1 ≤ 19) (h4 : 189 ≤ 10 * p.1 + 2 * p.2) : False := by
  U_cases hpU <;> linarith

/-- The regions of the apexes of `T_b^m` and `T_t^r` are disjoint inside `U`. -/
theorem excl36 {p : Point} (hpU : p ∈ U) (h2 : 6 * p.1 - 20 * p.2 - 21 ≤ 0) (h3 : 19 ≤ p.1) :
    False := by
  U_cases hpU <;> linarith

/-- The regions of the apexes of `T_t^ℓ` and `T_t^m` are disjoint inside `U`. -/
theorem excl24 {p : Point} (hpU : p ∈ U) (h1 : 5 * p.1 + p.2 ≤ 29 / 2) (h2 : 3 ≤ p.1) : False := by
  U_cases hpU <;> linarith

/-- **Lemma 5.** A guard set with at most three guards has exactly one guard on each of the
lines `l_ℓ, l_m, l_r`, and no other guard. -/
theorem three_lines {G : Finset Point} (hG : P.IsGuardSet (G : Set Point)) (hcard : G.card ≤ 3) :
    ∃ h x k : ℝ, (∀ g ∈ G, g = gL h ∨ g = gM x ∨ g = gR k) ∧ gL h ∈ G ∧ gM x ∈ G ∧ gR k ∈ G ∧
      gL h ∈ U ∧ gM x ∈ U ∧ gR k ∈ U := by
  have hU : ∀ g ∈ G, g ∈ U := fun g hg => filled_eq_U ▸ hG.1 hg
  obtain ⟨g1, hg1, s1⟩ := hG.2 _ (vtx_mem (by norm_num) vtx2)
  obtain ⟨g2, hg2, s2⟩ := hG.2 _ (vtx_mem (by norm_num) vtx43)
  obtain ⟨g3, hg3, s3⟩ := hG.2 _ (vtx_mem (by norm_num) vtx5)
  obtain ⟨g4, hg4, s4⟩ := hG.2 _ (vtx_mem (by norm_num) vtx28)
  obtain ⟨g5, hg5, s5⟩ := hG.2 _ (vtx_mem (by norm_num) vtx16)
  obtain ⟨g6, hg6, s6⟩ := hG.2 _ (vtx_mem (by norm_num) vtx25)
  have f1 := see_a1 (hU g1 hg1) s1
  have f2 := see_a2 (hU g2 hg2) s2
  have f3 := see_a3 (hU g3 hg3) s3
  have f4 := see_a4 (hU g4 hg4) s4
  have f5 := see_a5 (hU g5 hg5) s5
  have f6 := see_a6 (hU g6 hg6) s6
  have bd1 := U_bounds (hU g1 hg1)
  have bd2 := U_bounds (hU g2 hg2)
  have bd6 := U_bounds (hU g6 hg6)
  have n13 : g1 ≠ g3 := by rintro rfl; linarith [f3.1]
  have n15 : g1 ≠ g5 := by rintro rfl; linarith [f5.2]
  have n35 : g3 ≠ g5 := by rintro rfl; exact excl35 (hU g3 hg3) f3.1 f3.2 f5.1 f5.2
  have hGeq : ({g1, g3, g5} : Finset Point) = G := by
    apply Finset.eq_of_subset_of_card_le
    · intro g hg
      simp only [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simp [n13, n15]),
        Finset.card_insert_of_notMem (by simp [n35]), Finset.card_singleton]
      exact hcard
  have hmem : ∀ g ∈ G, g = g1 ∨ g = g3 ∨ g = g5 := by
    intro g hg
    rw [← hGeq] at hg
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hg
  have e21 : g2 = g1 := by
    rcases hmem g2 hg2 with h | h | h
    · exact h
    · subst h; linarith [f2.2, f3.1, f3.2]
    · subst h; linarith [f2.2, f5.2]
  have e43 : g4 = g3 := by
    rcases hmem g4 hg4 with h | h | h
    · subst h; linarith [f4.2.2]
    · exact h
    · subst h; linarith [f4.1, f4.2.1, f5.2]
  have e65 : g6 = g5 := by
    rcases hmem g6 hg6 with h | h | h
    · subst h; linarith
    · subst h; exact (excl36 (hU g6 hg6) f3.2 f6).elim
    · exact h
  subst e21 e43 e65
  have q1 : g2 = gL g2.2 := Prod.ext (by simp only [gL]; linarith [f2.1]) rfl
  have q3 : g4 = gM g4.1 := Prod.ext rfl (by simp only [gM]; linarith [f3.2, f4.2.1])
  have q5 : g6 = gR g6.2 := Prod.ext (by simp only [gR]; linarith [f5.1]) rfl
  refine ⟨g2.2, g4.1, g6.2, ?_, q1 ▸ hg2, q3 ▸ hg4, q5 ▸ hg6, q1 ▸ hU _ hg2, q3 ▸ hU _ hg4,
    q5 ▸ hU _ hg6⟩
  intro g hg
  rcases hmem g hg with rfl | rfl | rfl
  · exact Or.inl q1
  · exact Or.inr (Or.inl q3)
  · exact Or.inr (Or.inr q5)

/-! ### The rectangular pockets (Lemma 6) -/

theorem see_b1 {p : Point} (hpU : p ∈ U) (hs : P.Sees p ((21/2 : ℝ), (8 : ℝ))) : 21 / 2 ≤ p.1 := by
  obtain ⟨b1, b2, b3, b4⟩ := U_bounds hpU
  by_contra hc; push Not at hc
  refine not_sees_wit (p := ((21/2 : ℝ), (8 : ℝ))) (q := p) (t := 1/10) (by norm_num)
    (by norm_num) ?_ (sees_symm hs)
  intro hw; U_cases hw <;> linarith

theorem see_b2 {p : Point} (hpU : p ∈ U) (hs : P.Sees p ((53/5 : ℝ), (8 : ℝ))) : p.1 ≤ 53 / 5 := by
  obtain ⟨b1, b2, b3, b4⟩ := U_bounds hpU
  by_contra hc; push Not at hc
  refine not_sees_wit (p := ((53/5 : ℝ), (8 : ℝ))) (q := p) (t := 1/10) (by norm_num)
    (by norm_num) ?_ (sees_symm hs)
  intro hw; U_cases hw <;> linarith

theorem see_c1 {p : Point} (hpU : p ∈ U) (hs : P.Sees p ((-10 : ℝ), (9/5 : ℝ))) : p.2 ≤ 9 / 5 := by
  obtain ⟨b1, b2, b3, b4⟩ := U_bounds hpU
  by_contra hc; push Not at hc
  refine not_sees_wit (p := ((-10 : ℝ), (9/5 : ℝ))) (q := p) (t := 1/10) (by norm_num)
    (by norm_num) ?_ (sees_symm hs)
  intro hw; U_cases hw <;> linarith

theorem see_c2 {p : Point} (hpU : p ∈ U) (hs : P.Sees p ((-10 : ℝ), (17/10 : ℝ))) :
    17 / 10 ≤ p.2 := by
  obtain ⟨b1, b2, b3, b4⟩ := U_bounds hpU
  by_contra hc; push Not at hc
  refine not_sees_wit (p := ((-10 : ℝ), (17/10 : ℝ))) (q := p) (t := 1/10) (by norm_num)
    (by norm_num) ?_ (sees_symm hs)
  intro hw; U_cases hw <;> linarith

theorem see_d1 {p : Point} (hpU : p ∈ U) (hs : P.Sees p ((30 : ℝ), (1/2 : ℝ))) : 1 / 2 ≤ p.2 := by
  obtain ⟨b1, b2, b3, b4⟩ := U_bounds hpU
  by_contra hc; push Not at hc
  refine not_sees_wit (p := ((30 : ℝ), (1/2 : ℝ))) (q := p) (t := 1/10) (by norm_num)
    (by norm_num) ?_ (sees_symm hs)
  intro hw; U_cases hw <;> linarith

theorem see_d2 {p : Point} (hpU : p ∈ U) (hs : P.Sees p ((30 : ℝ), (3/5 : ℝ))) : p.2 ≤ 3 / 5 := by
  obtain ⟨b1, b2, b3, b4⟩ := U_bounds hpU
  by_contra hc; push Not at hc
  refine not_sees_wit (p := ((30 : ℝ), (3/5 : ℝ))) (q := p) (t := 1/10) (by norm_num)
    (by norm_num) ?_ (sees_symm hs)
  intro hw; U_cases hw <;> linarith

/-- `gR k` does not see the top-left corner of `R_m` (blocked by its right side). -/
theorem not_sees_gR_b1 {k : ℝ} (hk0 : -2 ≤ k) (hk : k < 8) : ¬ P.Sees (gR k) ((21/2 : ℝ), (8 : ℝ)) := by
  intro hs
  refine block_v (i := 34) (by norm_num) vtx34 vtx35 (p := ((21/2 : ℝ), (8 : ℝ))) (q := gR k)
    (by norm_num) (by simp only [gR]; norm_num) ?_ (sees_symm hs)
  left; simp only [gR]; constructor <;> nlinarith

/-- `gL h` does not see the top-right corner of `R_m` (blocked by its left side). -/
theorem not_sees_gL_b2 {h : ℝ} (hh0 : -2 ≤ h) (hh : h < 8) : ¬ P.Sees (gL h) ((53/5 : ℝ), (8 : ℝ)) := by
  refine block_v (i := 36) (by norm_num) vtx36 vtx37 (p := gL h) (q := ((53/5 : ℝ), (8 : ℝ)))
    (by simp only [gL]; norm_num) (by norm_num) ?_
  right; simp only [gL]; constructor <;> nlinarith

/-- A guard with `2 ≤ x ≤ 19` and height `< 3/2` does not see the corner `(-10, 1.8)`. -/
theorem not_sees_c1 {p : Point} (h1 : 2 ≤ p.1) (h2 : p.1 ≤ 19) (h3 : p.2 < 3 / 2) :
    ¬ P.Sees p ((-10 : ℝ), (9/5 : ℝ)) := by
  refine block_h (i := 48) (by norm_num) vtx48 vtx49 (by linarith) (by norm_num) ?_
  left; constructor <;> nlinarith

/-- A guard with `x ≥ 2` and height `> 4/5` does not see the corner `(30, 0.5)`. -/
theorem not_sees_d1 {p : Point} (h1 : 2 ≤ p.1) (h2 : p.1 ≤ 19) (h3 : 4 / 5 < p.2) :
    ¬ P.Sees p ((30 : ℝ), (1/2 : ℝ)) := by
  intro hs
  refine block_h (i := 21) (by norm_num) vtx21 vtx22 (p := ((30 : ℝ), (1/2 : ℝ))) (q := p)
    (by norm_num) (by linarith) ?_ (sees_symm hs)
  right; constructor <;> nlinarith

/-- The middle guard does not see the corner `(-10, 1.7)`. -/
theorem not_sees_gM_c2 {x : ℝ} (hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5) :
    ¬ P.Sees (gM x) ((-10 : ℝ), (17/10 : ℝ)) := by
  intro hs
  refine block_v (i := 45) (by norm_num) vtx45 vtx46 (p := ((-10 : ℝ), (17/10 : ℝ))) (q := gM x)
    (by norm_num) (by simp only [gM]; linarith [hx.1]) ?_ (sees_symm hs)
  right; simp only [gM]; constructor <;> nlinarith [hx.1, hx.2]

/-- The middle guard does not see the corner `(30, 0.5)`. -/
theorem not_sees_gM_d1 {x : ℝ} (hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5) :
    ¬ P.Sees (gM x) ((30 : ℝ), (1/2 : ℝ)) := by
  refine block_v (i := 22) (by norm_num) vtx22 vtx23 (p := gM x) (q := ((30 : ℝ), (1/2 : ℝ)))
    (by simp only [gM]; linarith [hx.2]) (by norm_num) ?_
  left; simp only [gM]; constructor <;> nlinarith [hx.1, hx.2]

/-! ### Lemma 9: the corner `(12, -34/21)` -/

theorem not_sees_gR_v {k : ℝ} (hk : 1 / 2 ≤ k ∧ k < 6 / 5) :
    ¬ P.Sees (gR k) ((12 : ℝ), (-34/21 : ℝ)) := by
  intro hs
  refine block_h (i := 14) (by norm_num) vtx14 vtx15 (p := ((12 : ℝ), (-34/21 : ℝ))) (q := gR k)
    (by norm_num) (by simp only [gR]; linarith [hk.1]) ?_ (sees_symm hs)
  left; simp only [gR]; constructor <;> nlinarith [hk.1, hk.2]

theorem not_sees_gL_v {h : ℝ} (hh : 17 / 10 ≤ h ∧ h ≤ 9 / 5) :
    ¬ P.Sees (gL h) ((12 : ℝ), (-34/21 : ℝ)) := by
  refine block_v (i := 9) (by norm_num) vtx9 vtx10 (p := gL h) (q := ((12 : ℝ), (-34/21 : ℝ)))
    (by simp only [gL]; norm_num) (by norm_num) ?_
  left; simp only [gL]; constructor <;> nlinarith [hh.1, hh.2]

theorem not_sees_gM_v {x : ℝ} (hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5) :
    ¬ P.Sees (gM x) ((12 : ℝ), (-34/21 : ℝ)) := by
  intro hs
  refine block_h (i := 10) (by norm_num) vtx10 vtx11 (p := ((12 : ℝ), (-34/21 : ℝ))) (q := gM x)
    (by norm_num) (by simp only [gM]; linarith [hx.1]) ?_ (sees_symm hs)
  left; simp only [gM]; constructor <;> nlinarith [hx.1, hx.2]

/-! ### Lemmas 6 and 9 -/

/-- **Lemmas 5, 6 and 9.** A guard set with at most three guards consists of `(2, h)`,
`(x, 0.3 x - 1.05)` and `(19, k)` with `h ∈ [0.5, 0.6]`, `x ∈ [10.5, 10.6]`, `k ∈ [1.7, 1.8]`. -/
theorem guard_ranges {G : Finset Point} (hG : P.IsGuardSet (G : Set Point)) (hcard : G.card ≤ 3) :
    ∃ h x k : ℝ, (∀ g ∈ G, g = gL h ∨ g = gM x ∨ g = gR k) ∧ gL h ∈ G ∧ gM x ∈ G ∧ gR k ∈ G ∧
      (1 / 2 ≤ h ∧ h ≤ 3 / 5) ∧ (21 / 2 ≤ x ∧ x ≤ 53 / 5) ∧ (17 / 10 ≤ k ∧ k ≤ 9 / 5) := by
  obtain ⟨h, x, k, hall, hLG, hMG, hRG, hLU, hMU, hRU⟩ := three_lines hG hcard
  have seen : ∀ q ∈ P.filled, P.Sees (gL h) q ∨ P.Sees (gM x) q ∨ P.Sees (gR k) q := by
    intro q hq
    obtain ⟨g, hg, hs⟩ := hG.2 q hq
    rcases hall g hg with rfl | rfl | rfl
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr hs)
  have bL := U_bounds hLU; have bR := U_bounds hRU
  simp only [gL, gR] at bL bR
  have hL4 : h ≤ 9 / 2 := by
    have hLU' := hLU; simp only [gL] at hLU'; U_cases hLU' <;> linarith
  have hR4 : k ≤ 9 / 2 := by
    have hRU' := hRU; simp only [gR] at hRU'; U_cases hRU' <;> linarith
  -- the top corners of `R_m`
  have hx1 : 21 / 2 ≤ x := by
    rcases seen _ (vtx_mem (by norm_num) vtx36) with s | s | s
    · have := see_b1 hLU s; simp only [gL] at this; linarith
    · have := see_b1 hMU s; simpa only [gM] using this
    · exact absurd s (not_sees_gR_b1 (by linarith) (by linarith))
  have hx2 : x ≤ 53 / 5 := by
    rcases seen _ (vtx_mem (by norm_num) vtx35) with s | s | s
    · exact absurd s (not_sees_gL_b2 (by linarith) (by linarith))
    · have := see_b2 hMU s; simpa only [gM] using this
    · have := see_b2 hRU s; simp only [gR] at this; linarith
  have hx : 21 / 2 ≤ x ∧ x ≤ 53 / 5 := ⟨hx1, hx2⟩
  -- the far corners of `R_ℓ` and `R_r`
  have sc1 := seen _ (vtx_mem (by norm_num) vtx47)
  have sc2 := seen _ (vtx_mem (by norm_num) vtx48)
  have sd1 := seen _ (vtx_mem (by norm_num) vtx20)
  have sd2 := seen _ (vtx_mem (by norm_num) vtx21)
  have nMc1 : ¬ P.Sees (gM x) ((-10 : ℝ), (9/5 : ℝ)) := by
    intro s; have := see_c1 hMU s; simp only [gM] at this; linarith
  have nMd2 : ¬ P.Sees (gM x) ((30 : ℝ), (3/5 : ℝ)) := by
    intro s; have := see_d2 hMU s; simp only [gM] at this; linarith
  have nMc2 := not_sees_gM_c2 hx
  have nMd1 := not_sees_gM_d1 hx
  -- seeing the corners forces the heights
  have Lc1 : P.Sees (gL h) ((-10 : ℝ), (9/5 : ℝ)) → 3 / 2 ≤ h ∧ h ≤ 9 / 5 := by
    intro s
    refine ⟨?_, by have := see_c1 hLU s; simpa only [gL] using this⟩
    by_contra hc; push Not at hc
    exact not_sees_c1 (p := gL h) (by simp [gL]) (by simp only [gL]; norm_num) hc s
  have Rc1 : P.Sees (gR k) ((-10 : ℝ), (9/5 : ℝ)) → 3 / 2 ≤ k ∧ k ≤ 9 / 5 := by
    intro s
    refine ⟨?_, by have := see_c1 hRU s; simpa only [gR] using this⟩
    by_contra hc; push Not at hc
    exact not_sees_c1 (p := gR k) (by simp only [gR]; norm_num) (by simp [gR]) hc s
  have Ld1 : P.Sees (gL h) ((30 : ℝ), (1/2 : ℝ)) → 1 / 2 ≤ h ∧ h ≤ 4 / 5 := by
    intro s
    refine ⟨by have := see_d1 hLU s; simpa only [gL] using this, ?_⟩
    by_contra hc; push Not at hc
    exact not_sees_d1 (p := gL h) (by simp [gL]) (by simp only [gL]; norm_num) hc s
  have Rd1 : P.Sees (gR k) ((30 : ℝ), (1/2 : ℝ)) → 1 / 2 ≤ k ∧ k ≤ 4 / 5 := by
    intro s
    refine ⟨by have := see_d1 hRU s; simpa only [gR] using this, ?_⟩
    by_contra hc; push Not at hc
    exact not_sees_d1 (p := gR k) (by simp only [gR]; norm_num) (by simp [gR]) hc s
  have Lc2 : P.Sees (gL h) ((-10 : ℝ), (17/10 : ℝ)) → 17 / 10 ≤ h := fun s => by
    have := see_c2 hLU s; simpa only [gL] using this
  have Rc2 : P.Sees (gR k) ((-10 : ℝ), (17/10 : ℝ)) → 17 / 10 ≤ k := fun s => by
    have := see_c2 hRU s; simpa only [gR] using this
  have Ld2 : P.Sees (gL h) ((30 : ℝ), (3/5 : ℝ)) → h ≤ 3 / 5 := fun s => by
    have := see_d2 hLU s; simpa only [gL] using this
  have Rd2 : P.Sees (gR k) ((30 : ℝ), (3/5 : ℝ)) → k ≤ 3 / 5 := fun s => by
    have := see_d2 hRU s; simpa only [gR] using this
  rcases sc1 with c1 | c1 | c1
  · -- the guard on `l_ℓ` is the high one: then the corner `(12, -34/21)` is unseen (Lemma 9)
    exfalso
    have hc1 := Lc1 c1
    have hk1 : 1 / 2 ≤ k ∧ k ≤ 4 / 5 := by
      rcases sd1 with d | d | d
      · have := Ld1 d; linarith
      · exact absurd d nMd1
      · exact Rd1 d
    have hk2 : k ≤ 3 / 5 := by
      rcases sd2 with d | d | d
      · have := Ld2 d; linarith
      · exact absurd d nMd2
      · exact Rd2 d
    have hh2 : 17 / 10 ≤ h := by
      rcases sc2 with c | c | c
      · exact Lc2 c
      · exact absurd c nMc2
      · have := Rc2 c; linarith
    rcases seen _ (vtx_mem (by norm_num) vtx12) with s | s | s
    · exact not_sees_gL_v ⟨hh2, hc1.2⟩ s
    · exact not_sees_gM_v hx s
    · exact not_sees_gR_v ⟨by linarith, by linarith⟩ s
  · exact absurd c1 nMc1
  · have hc1 := Rc1 c1
    have hh1 : 1 / 2 ≤ h ∧ h ≤ 4 / 5 := by
      rcases sd1 with d | d | d
      · exact Ld1 d
      · exact absurd d nMd1
      · have := Rd1 d; linarith
    have hh2 : h ≤ 3 / 5 := by
      rcases sd2 with d | d | d
      · exact Ld2 d
      · exact absurd d nMd2
      · have := Rd2 d; linarith
    have hk2 : 17 / 10 ≤ k := by
      rcases sc2 with c | c | c
      · have := Lc2 c; linarith
      · exact absurd c nMc2
      · exact Rc2 c
    exact ⟨h, x, k, hall, hLG, hMG, hRG, ⟨hh1.1, hh2⟩, hx, ⟨hk2, hc1.2⟩⟩

end

end ArtGallery.Irrational
