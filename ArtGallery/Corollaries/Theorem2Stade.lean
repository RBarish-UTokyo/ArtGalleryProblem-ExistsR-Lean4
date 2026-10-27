module

public import ArtGallery.Stade.API
public import ArtGallery.Stade.Counting
public import ArtGallery.Stade.Simple
public import ArtGallery.ETR.REV
public import ArtGallery.Invariance.Affine
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Theorem 2 via Stade's construction

For a real algebraic number `α`:

1. `α` is a root of a nonzero integer polynomial `p` (`IsFractionRing.isAlgebraic_iff`), and
   `α` is the only root of `p` in some open interval `(a, b)` with rational ends
   (`isolate_root`: the other roots form a finite, hence closed, set).
2. The ETR formula `φ = algFormula p a b` (`p(x₀) = 0 ∧ a < x₀ ∧ x₀ < b`, with integer
   constants written as terms) has the unique solution `x₀ = α`.
3. Stade's polygon `poly n Φ` for the ETR-INV-REV instance `Φ = etrToREV φ` on
   `n = etrToREVVars φ` variables: every guard set has at least `guards n Φ` guards
   (`card_le_of_boundaryGuard`), a solution gives a guard set of that cardinality
   (`guardSet_of_sat`), and a guard set of that cardinality contains the guard
   `(varX 0, varY0 + 2 v 0)` for a solution `v` (`sat_of_boundaryGuard`), where
   `v 0 = ε x₀ + 7/8` for a satisfying assignment `x` of `φ` (`etrToREV_sound`), so `x₀ = α`.
   Hence the optimal guard sets are exactly the guard sets of cardinality `guards n Φ`, and
   each contains a guard with `y`-coordinate `2 ε α + varY0 + 7/4`.
4. The invertible affine map `(x, y) ↦ ((y - e) / c, x)` (`swapShiftA`, with `c = 2 ε`,
   `e = varY0 + 7/4`) keeps the vertices rational and moves this guard to `x`-coordinate `α`;
   guard sets and cardinalities are transported.

This proof does not use Theorem 54 (`etrinv_guard_correspondence`).
-/

@[expose] public section

namespace ArtGallery

namespace Corollaries

open ETR Polynomial Set ArtGallery.Hardening.Invariance


/-! ### Integer constants and polynomials as terms -/

/-- The natural number `k` as the term `0 + 1 + ⋯ + 1`. -/
def natTerm : ℕ → Term
  | 0 => .zero
  | k + 1 => .add (natTerm k) .one

/-- The integer `z` as a term. -/
def intTerm : ℤ → Term
  | .ofNat k => natTerm k
  | .negSucc k => .sub .zero (natTerm (k + 1))

/-- The power `x₀ ^ k` as a term. -/
def powTerm : ℕ → Term
  | 0 => .one
  | k + 1 => .mul (powTerm k) (.var 0)

/-- The polynomial `∑_{j < k} f j · x₀ ^ j` as a term. -/
def polyTerm (f : ℕ → ℤ) : ℕ → Term
  | 0 => .zero
  | k + 1 => .add (polyTerm f k) (.mul (intTerm (f k)) (powTerm k))

theorem natTerm_eval (x : ℕ → ℝ) (k : ℕ) : (natTerm k).eval x = k := by
  induction k with
  | zero => simp [natTerm, Term.eval]
  | succ k ih => simp only [natTerm, Term.eval, ih]; push_cast; ring

theorem intTerm_eval (x : ℕ → ℝ) (z : ℤ) : (intTerm z).eval x = z := by
  cases z with
  | ofNat k => simp only [intTerm, natTerm_eval]; simp
  | negSucc k =>
    simp only [intTerm, Term.eval, natTerm_eval, Int.cast_negSucc]; push_cast; ring

theorem powTerm_eval (x : ℕ → ℝ) (k : ℕ) : (powTerm k).eval x = x 0 ^ k := by
  induction k with
  | zero => simp [powTerm, Term.eval]
  | succ k ih => simp only [powTerm, Term.eval, ih]; ring

theorem polyTerm_eval (x : ℕ → ℝ) (f : ℕ → ℤ) (k : ℕ) :
    (polyTerm f k).eval x = ∑ j ∈ Finset.range k, (f j : ℝ) * x 0 ^ j := by
  induction k with
  | zero => simp [polyTerm, Term.eval]
  | succ k ih =>
    simp only [polyTerm, Term.eval, ih, intTerm_eval, powTerm_eval, Finset.sum_range_succ]

theorem natTerm_varsLt (k : ℕ) : (natTerm k).VarsLt 1 := by
  induction k with
  | zero => trivial
  | succ k ih => exact ⟨ih, trivial⟩

theorem intTerm_varsLt (z : ℤ) : (intTerm z).VarsLt 1 := by
  cases z with
  | ofNat k => exact natTerm_varsLt k
  | negSucc k => exact ⟨trivial, natTerm_varsLt _⟩

theorem powTerm_varsLt (k : ℕ) : (powTerm k).VarsLt 1 := by
  induction k with
  | zero => trivial
  | succ k ih => exact ⟨ih, Nat.zero_lt_one⟩

theorem polyTerm_varsLt (f : ℕ → ℤ) (k : ℕ) : (polyTerm f k).VarsLt 1 := by
  induction k with
  | zero => trivial
  | succ k ih => exact ⟨ih, intTerm_varsLt _, powTerm_varsLt _⟩

/-- The formula `p(x₀) = 0 ∧ a < x₀ ∧ x₀ < b`. -/
noncomputable def algFormula (p : ℤ[X]) (a b : ℚ) : Formula :=
  .and (.eq (polyTerm p.coeff (p.natDegree + 1)) .zero)
    (.and (.lt (intTerm a.num) (.mul (intTerm a.den) (.var 0)))
      (.lt (.mul (intTerm b.den) (.var 0)) (intTerm b.num)))

theorem algFormula_varsLt (p : ℤ[X]) (a b : ℚ) : (algFormula p a b).VarsLt 1 :=
  ⟨⟨polyTerm_varsLt _ _, trivial⟩, ⟨intTerm_varsLt _, intTerm_varsLt _, Nat.zero_lt_one⟩,
    ⟨intTerm_varsLt _, Nat.zero_lt_one⟩, intTerm_varsLt _⟩

theorem algFormula_holds (p : ℤ[X]) (a b : ℚ) (x : ℕ → ℝ) :
    (algFormula p a b).Holds x ↔ aeval (x 0) p = 0 ∧ (a : ℝ) < x 0 ∧ x 0 < b := by
  have ha : (0 : ℝ) < a.den := by exact_mod_cast a.den_pos
  have hb : (0 : ℝ) < b.den := by exact_mod_cast b.den_pos
  simp only [algFormula, Formula.Holds, Term.eval, polyTerm_eval, intTerm_eval,
    aeval_eq_sum_range, zsmul_eq_mul, Rat.cast_def, Int.cast_natCast]
  rw [div_lt_iff₀ ha, lt_div_iff₀ hb, mul_comm (x 0) (a.den : ℝ), mul_comm (x 0) (b.den : ℝ)]

/-- **Root isolation.** Some open interval with rational ends around `α` contains no root of
the nonzero integer polynomial `p` other than `α`. -/
theorem isolate_root {p : ℤ[X]} (hp : p ≠ 0) (α : ℝ) :
    ∃ a b : ℚ, (a : ℝ) < α ∧ α < b ∧
      ∀ r : ℝ, aeval r p = 0 → (a : ℝ) < r → r < b → r = α := by
  have hS : IsClosed (p.rootSet ℝ \ {α}) := ((rootSet_finite p ℝ).sdiff).isClosed
  have hαS : α ∈ (p.rootSet ℝ \ {α})ᶜ := fun h => h.2 rfl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hS.isOpen_compl α hαS
  obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn (show α - ε < α by linarith)
  obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn (show α < α + ε by linarith)
  refine ⟨a, b, ha₂, hb₁, fun r hr har hrb => ?_⟩
  have hrb' : r ∈ Metric.ball α ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  have hroot : r ∈ p.rootSet ℝ := mem_rootSet.2 ⟨hp, hr⟩
  by_contra hne
  exact hball hrb' ⟨hroot, hne⟩

/-! ### The affine map `(x, y) ↦ ((x - d) / c, y)` -/

/-- The invertible affine map `(x, y) ↦ ((x - d) / c, y)` for `c ≠ 0`. -/
noncomputable def shiftA (c d : ℝ) (hc : c ≠ 0) : Point ≃ᵃ[ℝ] Point :=
  (AffineEquiv.constVAdd ℝ Point ((-d, 0) : Point)).trans
    ((LinearEquiv.prodCongr (LinearEquiv.smulOfNeZero ℝ ℝ c⁻¹ (inv_ne_zero hc))
      (LinearEquiv.refl ℝ ℝ)).toAffineEquiv)

theorem shiftA_apply (c d : ℝ) (hc : c ≠ 0) (p : Point) :
    shiftA c d hc p = ((p.1 - d) / c, p.2) := by
  obtain ⟨u, v⟩ := p
  simp only [shiftA, AffineEquiv.trans_apply, AffineEquiv.constVAdd_apply,
    LinearEquiv.coe_toAffineEquiv, vadd_eq_add, Prod.mk_add_mk, LinearEquiv.prodCongr_apply,
    LinearEquiv.smulOfNeZero_apply, LinearEquiv.refl_apply, smul_eq_mul, Prod.mk.injEq]
  constructor <;> ring

variable (A : Point ≃ᵃ[ℝ] Point) (P : Polygon)

theorem sees_map {p q : Point} : (mapPoly A P).Sees (A p) (A q) ↔ P.Sees p q := by
  unfold Polygon.Sees
  rw [filled_mapPoly, ← image_segment', image_subset_image_iff A.injective]

/-- Guard sets are mapped to guard sets. -/
theorem isGuardSet_map {G : Finset Point} (hG : P.IsGuardSet (G : Set Point)) :
    (mapPoly A P).IsGuardSet ((G.image A : Finset Point) : Set Point) := by
  refine ⟨?_, ?_⟩
  · intro g hg
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    rw [filled_mapPoly]; exact mem_image_of_mem _ (hG.1 hg')
  · intro p hp
    rw [filled_mapPoly] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    obtain ⟨g, hg, hs⟩ := hG.2 p' hp'
    exact ⟨A g, by simp only [Finset.coe_image]; exact mem_image_of_mem _ hg,
      (sees_map A P).2 hs⟩

/-- Guard sets of the image polygon come from guard sets. -/
theorem isGuardSet_of_map {G : Finset Point}
    (hG : (mapPoly A P).IsGuardSet (G : Set Point)) :
    P.IsGuardSet ((G.image A.symm : Finset Point) : Set Point) := by
  refine ⟨?_, ?_⟩
  · intro g hg
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    have := hG.1 hg'
    rw [filled_mapPoly] at this
    obtain ⟨x, hx, hxg⟩ := this
    rw [← hxg, AffineEquiv.symm_apply_apply]; exact hx
  · intro p hp
    have hp' : A p ∈ (mapPoly A P).filled := by
      rw [filled_mapPoly]; exact mem_image_of_mem _ hp
    obtain ⟨g, hg, hs⟩ := hG.2 _ hp'
    refine ⟨A.symm g, by simp only [Finset.coe_image]; exact mem_image_of_mem _ hg, ?_⟩
    rw [← sees_map A P, AffineEquiv.apply_symm_apply]; exact hs

/-- The invertible affine map `(x, y) ↦ ((y - e) / c, x)` for `c ≠ 0`. -/
noncomputable def swapShiftA (c e : ℝ) (hc : c ≠ 0) : Point ≃ᵃ[ℝ] Point :=
  (LinearEquiv.prodComm ℝ ℝ ℝ).toAffineEquiv.trans (shiftA c e hc)

theorem swapShiftA_apply (c e : ℝ) (hc : c ≠ 0) (p : Point) :
    swapShiftA c e hc p = ((p.2 - e) / c, p.1) := by
  simp only [swapShiftA, AffineEquiv.trans_apply, LinearEquiv.coe_toAffineEquiv,
    LinearEquiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, shiftA_apply]

/-- The formula `algFormula p a b` mentions the variable `x₀`. -/
theorem algFormula_varBound_pos (p : ℤ[X]) (a b : ℚ) : 0 < (algFormula p a b).varBound := by
  simp only [algFormula, Formula.varBound, Term.varBound]
  omega

/-- The ETR-INV-REV instance of a formula has at least one variable. -/
theorem etrToREVVars_pos' (φ : ETR.Formula) : 0 < etrToREVVars φ := by
  have := etrHalfIndex_lt φ
  unfold etrToREVVars; omega

end Corollaries

open Corollaries Polynomial ArtGallery.Hardening.Invariance ArtGallery.Stade

/-- **Theorem 2** (proof through Stade's construction, without Theorem 54). For every real
algebraic number `α` there is a simple polygon with rational vertex coordinates that has an
optimal guard set, and every optimal guard set of it contains a guard with `x`-coordinate
`α`. -/
theorem algebraic_guard_coordinate' (α : ℝ) (hα : IsAlgebraic ℚ α) :
    ∃ V : List (ℚ × ℚ),
      (Polygon.mk (V.map ratPoint)).Simple ∧
      (∃ G : Finset Point, (Polygon.mk (V.map ratPoint)).IsOptimalGuardSet G) ∧
      ∀ G : Finset Point, (Polygon.mk (V.map ratPoint)).IsOptimalGuardSet G →
        ∃ p ∈ G, p.1 = α := by
  obtain ⟨p, hp, hpα⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).2 hα
  obtain ⟨a, b, haα, hαb, huniq⟩ := isolate_root hp α
  set φ := algFormula p a b
  have hsat : φ.Satisfiable :=
    ⟨fun _ => α, (algFormula_holds p a b _).2 ⟨hpα, haα, hαb⟩⟩
  set n := etrToREVVars φ
  set Φ := etrToREV φ
  have hΦ : ∀ c ∈ Φ, c.VarsLt n := etrToREV_vars φ
  have hn : 0 < n := etrToREVVars_pos' φ
  set g := guards n Φ
  -- the affine map
  set c : ℚ := 2 * etrScale φ
  set e : ℚ := varY0 n Φ + 7 / 4
  have hc : (c : ℝ) ≠ 0 := by
    have := etrScale_pos φ
    simp only [c]; push_cast; positivity
  set A := swapShiftA c e hc
  set P : Polygon := Polygon.mk ((poly n Φ).map ratPoint)
  set V' : List (ℚ × ℚ) := (poly n Φ).map (fun q => ((q.2 - e) / c, q.1))
  have hV' : Polygon.mk (V'.map ratPoint) = mapPoly A P := by
    simp only [V', P, mapPoly, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q _
    simp only [Function.comp_apply, A, swapShiftA_apply, ratPoint]
    push_cast; rfl
  -- the three facts on Stade's polygon
  have hlow : ∀ G : Finset Point, P.IsGuardSet (G : Set Point) → g ≤ G.card := fun G hG =>
    card_le_of_boundaryGuard n Φ hΦ G (isBoundaryGuardSet_of_isGuardSet hG)
  obtain ⟨v₀, hv₀, hs₀⟩ := etrToREV_complete φ hsat
  obtain ⟨G₀, hG₀c, hG₀, -⟩ := guardSet_of_sat n Φ hΦ hn hv₀ hs₀
  -- every guard set of the image polygon has at least `g` guards
  have hlow' : ∀ G : Finset Point, (mapPoly A P).IsGuardSet (G : Set Point) → g ≤ G.card :=
    fun G hG => by
      have := hlow _ (isGuardSet_of_map A P hG)
      rwa [Finset.card_image_of_injective _ A.symm.injective] at this
  have hG₀' := isGuardSet_map A P hG₀
  have hG₀card : (G₀.image A).card = g := by
    rw [Finset.card_image_of_injective _ A.injective, hG₀c]
  refine ⟨V', ?_, ?_, ?_⟩
  · rw [hV']; exact (simple_mapPoly_iff A P).2 (simple n Φ)
  · rw [hV']
    exact ⟨G₀.image A, hG₀', fun G' hG' => hG₀card ▸ hlow' G' hG'⟩
  · rw [hV']
    intro G hG
    have hcard : G.card = g :=
      le_antisymm (hG₀card ▸ hG.2 _ hG₀') (hlow' G hG.1)
    obtain ⟨v, -, hs, hvG⟩ := sat_of_boundaryGuard n Φ hΦ _
      (isBoundaryGuardSet_of_isGuardSet (isGuardSet_of_map A P hG.1))
      (by rw [Finset.card_image_of_injective _ A.symm.injective, hcard])
    obtain ⟨x, hx, hxv⟩ := etrToREV_sound φ v hs
    have hx0 := (algFormula_holds p a b x).1 hx
    have hxα : x 0 = α := huniq _ hx0.1 hx0.2.1 hx0.2.2
    have hv0 : v 0 = (etrScale φ : ℝ) * α + 7 / 8 := by
      rw [hxv 0 (algFormula_varBound_pos p a b), hxα]
    obtain ⟨q, hq, hqe⟩ := Finset.mem_image.1 (hvG 0 hn)
    refine ⟨q, hq, ?_⟩
    have : q = A ((varX n Φ 0 : ℝ), (varY0 n Φ : ℝ) + 2 * v 0) := by
      rw [← hqe, AffineEquiv.apply_symm_apply]
    have hε : (etrScale φ : ℝ) ≠ 0 := by exact_mod_cast (etrScale_pos φ).ne'
    rw [this, swapShiftA_apply, hv0]
    simp only [c, e]
    push_cast
    field_simp
    ring

end ArtGallery

end
