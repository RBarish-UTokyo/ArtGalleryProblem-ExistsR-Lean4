module

public import ArtGallery.Hardness.BP.Assemble.UnitChain
public import ArtGallery.Hardness.BP.Assemble.Global
public import ArtGallery.Hardness.Sec5.Assemble.Simple

/-!
# Boundary-point variant: the polygon `constructBP Φ n` is simple

**Main theorem** `constructBP_simple`: for every instance with all variable indices `< n`, the
polygon `constructBP Φ n` is simple and counter-clockwise (`n = 0`: the triangle
`(0,0), (1,0), (0,1)`), as `Sec5/Assemble/Simple.lean`:

* the units of `unitSpecs n Φ` are admissible (`Sec5.UnitOK`, `unitSpecs_ok`; the boundary-point
  templates have as many receivers as the Section 5 templates, `length_tmplTBP_eq`), at most `N`
  per side; hence their corridor inputs with the new receivers are good (`unitInputBP_good`);
* the unit chains are `UnitFeature`s (`unitChainBP_feature`, from `unit_featureBP`), and
  `global_simpleBP` assembles the polygon (`constructBP_global`, which also describes the boundary
  right of `x = S` and left of `x = X_L` and bounds it by `y ≤ S + 3N`).
-/

@[expose] public section

namespace ArtGallery.BP

open ArtGallery Set
open ArtGallery.Sec5
open ArtGallery.Sec5.Corridor (Input)
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

theorem length_tmplTBP_eq (k : Kind) : (tmplTBP k).length = (tmplT k).length := by
  cases k <;> rfl


/-! ### Good corridor inputs -/

theorem tmplTBP_ok (k : Kind) : ∀ τ < (tmplTBP k).length,
    (-50 ≤ ((tmplTBP k).getD τ (0, 0)).1 ∧ ((tmplTBP k).getD τ (0, 0)).1 ≤ 50 ∧
      -50 ≤ ((tmplTBP k).getD τ (0, 0)).2 ∧ ((tmplTBP k).getD τ (0, 0)).2 ≤ 50) ∧
    ((tmplTBP k).getD τ (0, 0)).1 + ((tmplTBP k).getD τ (0, 0)).2 =
      ((tmplTBP k).getD 0 (0, 0)).1 + ((tmplTBP k).getD 0 (0, 0)).2 - 27 * τ / 2 := by
  intro τ hτ
  cases k <;> simp only [tmplTBP, tmplTGEBP, tmplTLEBP, tmplTORBP, tmplTInvBP, List.length_cons,
    List.length_nil] at hτ <;> interval_cases τ <;> norm_num [tmplTBP, tmplTGEBP, tmplTLEBP, tmplTORBP, tmplTInvBP]

/-- **The corridor input of an admissible unit is good.** -/
theorem unitInputBP_good {n k m : ℕ} {u : UnitSpec} (hu : UnitOK n u) (hm : m < bigN n k)
    (hn : 4 * n ≤ bigN n k) : (unitInputBP n k m u).Good (bigN n k : ℚ) := by
  have hN2 : (2 : ℚ) ≤ bigN n k := by exact_mod_cast two_le_bigN
  have hm' : (m : ℚ) + 1 ≤ bigN n k := by exact_mod_cast hm
  have hn' : (4 * n : ℚ) ≤ bigN n k := by exact_mod_cast hn
  have hlen := length_tmplT u.kind
  rw [← length_tmplTBP_eq] at hlen
  have hnp : (unitInputBP n k m u).np = (tmplTBP u.kind).length :=
    hu.len.trans (length_tmplTBP_eq _).symm
  refine ⟨⟨⟨hN2, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [unitInputBP, S_cast]
  · simp only [unitInputBP, unitH]; have : (0 : ℚ) ≤ m := Nat.cast_nonneg m; linarith
  · simp only [unitInputBP, unitH]; linarith
  · rw [hnp]; omega
  · intro j hj
    have hj0 : j < u.work.length := by simpa [Input.np, unitInputBP] using hj
    have hσ := hu.lt _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj0]
                           exact List.getElem_mem _ : u.work.getD j 0 ∈ u.work)
    have : ((Input.sigma (unitInputBP n k m u) j : ℕ) : ℚ) + 1 ≤ 4 * n := by
      have : Input.sigma (unitInputBP n k m u) j + 1 ≤ 4 * n := by
        simp only [Input.sigma, unitInputBP]; omega
      exact_mod_cast this
    nlinarith
  · intro τ hτ
    exact (tmplTBP_ok u.kind τ (by rwa [hnp] at hτ)).1
  · intro τ hτ
    exact (tmplTBP_ok u.kind τ (by rwa [hnp] at hτ)).2
  · rw [hnp]; omega
  · intro j hj
    have hm := hu.mono
    rw [List.pairwise_iff_getElem] at hm
    have hj' : j + 1 < u.work.length := by simpa [Input.np, unitInputBP] using hj
    have := hm j (j + 1) (by omega) hj' (by omega)
    simp only [Input.sigma, unitInputBP, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj',
      List.getElem?_eq_getElem (show j < u.work.length by omega), Option.getD_some]
    exact this

/-! ### The main theorem -/

theorem unitChainBP_feature {n k m : ℕ} {u : UnitSpec} (hu : UnitOK n u) (hm : m < bigN n k)
    (hn : 4 * n ≤ bigN n k) :
    UnitFeature (S n k : ℝ) ((S n k : ℝ) + 3 * m + 1)
      (((Corridor.rho ((S n k : ℕ) : ℚ)) : ℚ) : ℝ) ((unitChainBP n k m u).map ratPoint) := by
  have h := unit_featureBP (unitInputBP_good hu hm hn) u.kind
  have e1 : (((unitInputBP n k m u).S : ℚ) : ℝ) = (S n k : ℝ) := by simp [unitInputBP]
  have e2 : (((unitInputBP n k m u).H : ℚ) : ℝ) = (S n k : ℝ) + 3 * m + 1 := by
    simp [unitInputBP, unitH]
  rw [e1, e2] at h
  exact h

/-- **The global facts** for `n ≥ 1`: the polygon is simple and counter-clockwise; right of
`x = S` its boundary consists of the right unit chains, left of `x = X_L` of the (mirrored) left
unit chains; it lies below `y = S + 3N`. -/
theorem constructBP_global {Φ : List ETRINV.Constraint} {n : ℕ} (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    (hn : 0 < n) :
    (Polygon.mk ((constructBP Φ n).map ratPoint)).Simple ∧
      (Polygon.mk ((constructBP Φ n).map ratPoint)).InteriorLeft ∧
      (∀ p ∈ (Polygon.mk ((constructBP Φ n).map ratPoint)).boundary,
        p.1 ≤ (S n (numC Φ) : ℝ) ∨
          ∃ f ∈ sideChainsRBP n (numC Φ) (unitSpecs n Φ).1, p ∈ chainSet f) ∧
      (∀ p ∈ (Polygon.mk ((constructBP Φ n).map ratPoint)).boundary,
        54 * (n : ℝ) - 12 - (S n (numC Φ) : ℝ) ≤ p.1 ∨
          ∃ f ∈ sideChainsRBP n (numC Φ) (unitSpecs n Φ).2, mirrorR n p ∈ chainSet f) ∧
      (∀ p ∈ (Polygon.mk ((constructBP Φ n).map ratPoint)).boundary,
        p.2 ≤ (S n (numC Φ) : ℝ) + 3 * (bigN n (numC Φ) : ℝ)) := by
  rw [constructBP_pos (by omega)]
  have hok := unitSpecs_ok hΦ
  have hNn := four_n_le_bigN (n := n) (k := numC Φ)
  have hρ : (0 : ℝ) < (((Corridor.rho ((S n (numC Φ) : ℕ) : ℚ)) : ℚ) : ℝ) := by
    have := S_pos_q (n := n) (k := numC Φ)
    have : (0 : ℚ) < Corridor.rho ((S n (numC Φ) : ℕ) : ℚ) := by
      simp only [Corridor.rho]; positivity
    exact_mod_cast this
  have hρ1 : (((Corridor.rho ((S n (numC Φ) : ℕ) : ℚ)) : ℚ) : ℝ) < 1 / 100 := by
    have := S_ge (n := n) (k := numC Φ)
    have h8 : (800000 : ℚ) ≤ ((S n (numC Φ) : ℕ) : ℚ) := by exact_mod_cast this
    have : Corridor.rho ((S n (numC Φ) : ℕ) : ℚ) < 1 / 100 := by
      simp only [Corridor.rho]; rw [div_lt_iff₀ (by positivity)]; linarith
    calc _ < ((1 / 100 : ℚ) : ℝ) := Rat.cast_lt.2 this
      _ = 1 / 100 := by norm_num
  have side : ∀ (us : List UnitSpec), (∀ u ∈ us, UnitOK n u) → us.length ≤ bigN n (numC Φ) →
      ∀ j (hj : j < (sideChainsRBP n (numC Φ) us).length),
        UnitFeature (S n (numC Φ) : ℝ) ((S n (numC Φ) : ℝ) + 3 * j + 1)
          (((Corridor.rho ((S n (numC Φ) : ℕ) : ℚ)) : ℚ) : ℝ) (sideChainsRBP n (numC Φ) us)[j] := by
    intro us hus hlen j hj
    have hj' : j < us.length := by simpa [sideChainsRBP, length_unitChainsBP] using hj
    simp only [sideChainsRBP, List.getElem_map]
    rw [getElem_unitChainsBP, Nat.zero_add]
    exact unitChainBP_feature (hus _ (List.getElem_mem _)) (by omega) hNn
  exact global_simpleBP hn hρ hρ1
    (side _ (fun u hu => hok u (List.mem_append_left _ hu)) (length_unitSpecs_fst n Φ))
    (side _ (fun u hu => hok u (List.mem_append_right _ hu)) (length_unitSpecs_snd n Φ))
    (length_unitSpecs_fst n Φ) (length_unitSpecs_snd n Φ)

/-- **The polygon of the reduction is simple and counter-clockwise** . -/
theorem constructBP_simple {Φ : List ETRINV.Constraint} {n : ℕ} (hΦ : ∀ c ∈ Φ, c.VarsLt n) :
    (Polygon.mk ((constructBP Φ n).map ratPoint)).Simple ∧
      (Polygon.mk ((constructBP Φ n).map ratPoint)).InteriorLeft := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [constructBP_zero]; exact ratPoint_triangle_ccw
  obtain ⟨h1, h2, -⟩ := constructBP_global hΦ hn
  exact ⟨h1, h2⟩

end ArtGallery.BP

end