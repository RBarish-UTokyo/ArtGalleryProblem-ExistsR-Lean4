module

public import ArtGallery.ETR.Reduction
public import ArtGallery.Hardness.Correspondence

/-!
# Theorem 55: the correspondence between ETR formulas and guard sets

`ArtGallery.etr_guard_correspondence` composes the reduction ETR → ETR-INV of §4
(`etrToINV`, with the affine correspondence `y i = ε x i + 7/8` of Lemma 19, `etrToINV_sound`)
with Theorem 54 (`etrinv_guard_correspondence`, ETR-INV → art gallery).  The constants are
`c i = ε = etrScale φ` and `d i = 7/8 + d' i`, where `d'` are the shifts of Theorem 54 for the
instance `etrToINV φ` on `max (etrToINVVars φ) n` variables.

For the variables `x i` with `φ.varBound ≤ i < n` (which `φ` does not mention), the assignment
is chosen so that `ε x i + 7/8 = y i`, where `y` is the ETR-INV solution read off the guard set;
this does not affect `φ.Holds x` (`holds_congr`).
-/

@[expose] public section

namespace ArtGallery

namespace Corollaries

/-- The value of a term only depends on the variables below a bound for its indices. -/
theorem term_eval_congr {n : ℕ} {x y : ℕ → ℝ} (h : ∀ i < n, x i = y i) :
    ∀ t : ETR.Term, t.VarsLt n → t.eval x = t.eval y
  | .var i, ht => h i ht
  | .zero, _ => rfl
  | .one, _ => rfl
  | .add s t, ⟨hs, ht⟩ => by
    simp only [ETR.Term.eval, term_eval_congr h s hs, term_eval_congr h t ht]
  | .sub s t, ⟨hs, ht⟩ => by
    simp only [ETR.Term.eval, term_eval_congr h s hs, term_eval_congr h t ht]
  | .mul s t, ⟨hs, ht⟩ => by
    simp only [ETR.Term.eval, term_eval_congr h s hs, term_eval_congr h t ht]

/-- Whether a formula holds only depends on the variables below a bound for its indices. -/
theorem holds_congr {n : ℕ} {x y : ℕ → ℝ} (h : ∀ i < n, x i = y i) :
    ∀ φ : ETR.Formula, φ.VarsLt n → (φ.Holds x ↔ φ.Holds y)
  | .eq s t, ⟨hs, ht⟩ => by
    simp only [ETR.Formula.Holds, term_eval_congr h s hs, term_eval_congr h t ht]
  | .lt s t, ⟨hs, ht⟩ => by
    simp only [ETR.Formula.Holds, term_eval_congr h s hs, term_eval_congr h t ht]
  | .le s t, ⟨hs, ht⟩ => by
    simp only [ETR.Formula.Holds, term_eval_congr h s hs, term_eval_congr h t ht]
  | .not φ, hφ => by
    simp only [ETR.Formula.Holds, holds_congr h φ hφ]
  | .and φ ψ, ⟨hφ, hψ⟩ => by
    simp only [ETR.Formula.Holds, holds_congr h φ hφ, holds_congr h ψ hψ]
  | .or φ ψ, ⟨hφ, hψ⟩ => by
    simp only [ETR.Formula.Holds, holds_congr h φ hφ, holds_congr h ψ hψ]

/-- A bound on the variable indices of an ETR-INV equation can be enlarged. -/
theorem constraint_varsLt_mono {n m : ℕ} (h : n ≤ m) :
    ∀ c : ETRINV.Constraint, c.VarsLt n → c.VarsLt m
  | .one _, hc => lt_of_lt_of_le hc h
  | .add _ _ _, ⟨h₁, h₂, h₃⟩ => ⟨by omega, by omega, by omega⟩
  | .inv _ _, ⟨h₁, h₂⟩ => ⟨by omega, by omega⟩

end Corollaries

open Corollaries

set_option linter.unusedVariables false in
/-- **Theorem 55.** For every ETR formula `φ` on the variables `x 0, …, x (n-1)` there is a
simple polygon with rational vertices, a number `g` and rational constants `c i ≠ 0`, `d i`
such that every guard set has at least `g` guards, `φ` is satisfiable iff a guard set of
cardinality `g` exists, and every guard set of cardinality `g` contains the guards
`(c i x i + d i, 0)` for some satisfying assignment `x` of `φ`. -/
theorem etr_guard_correspondence (φ : ETR.Formula) (n : ℕ) (hφ : φ.VarsLt n) :
    ∃ (V : List (ℚ × ℚ)) (g : ℕ) (c d : ℕ → ℚ),
      (∀ i, c i ≠ 0) ∧
      (Polygon.mk (V.map ratPoint)).Simple ∧
      (∀ G : Finset Point, (Polygon.mk (V.map ratPoint)).IsGuardSet (G : Set Point) →
        g ≤ G.card) ∧
      (φ.Satisfiable → (Polygon.mk (V.map ratPoint)).HasGuardSetOfCard g) ∧
      ∀ G : Finset Point, (Polygon.mk (V.map ratPoint)).IsGuardSet (G : Set Point) →
        G.card = g →
          ∃ x : ℕ → ℝ, φ.Holds x ∧ ∀ i < n, ((c i : ℝ) * x i + (d i : ℝ), (0 : ℝ)) ∈ G := by
  -- `hφ` is not needed: the variables of index `≥ φ.varBound` are unconstrained.
  have hΦ : ∀ c ∈ etrToINV φ, c.VarsLt (max (etrToINVVars φ) n) := fun c hc =>
    constraint_varsLt_mono (le_max_left _ _) c (etrToINV_vars φ c hc)
  obtain ⟨V, g, d, hS, hlow, hsound, hiff⟩ :=
    etrinv_guard_correspondence (etrToINV φ) (max (etrToINVVars φ) n) hΦ
  have hε : (0 : ℝ) < (etrScale φ : ℝ) := by exact_mod_cast etrScale_pos φ
  refine ⟨V, g, fun _ => etrScale φ, fun i => 7 / 8 + d i, fun _ => (etrScale_pos φ).ne', hS,
    hlow, ?_, ?_⟩
  · intro hsat
    obtain ⟨v, hv, hc⟩ := etrToINV_complete φ hsat
    obtain ⟨-, G, hG, hGg, -⟩ := (hiff v).1 ⟨fun i _ => hv i, hc⟩
    exact ⟨G, hG, hGg⟩
  · intro G hG hcard
    obtain ⟨y, ⟨-, hy⟩, hyG⟩ := hsound G hG hcard
    obtain ⟨x, hx, hxy⟩ := etrToINV_sound φ y hy
    refine ⟨fun i => if i < φ.varBound then x i else (y i - 7 / 8) / (etrScale φ : ℝ), ?_,
      fun i hi => ?_⟩
    · refine (holds_congr (fun i hi => ?_) φ φ.varsLt_varBound).1 hx
      simp only [hi, ↓reduceIte]
    · have hmem := hyG i (lt_of_lt_of_le hi (le_max_right _ _))
      convert hmem using 2
      simp only
      split_ifs with h
      · rw [hxy i h]; push_cast; ring
      · push_cast; field_simp; ring

end ArtGallery

end
