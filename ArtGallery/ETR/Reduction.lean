module

public import ArtGallery.ETR.CircuitSem
public import ArtGallery.ETR.ChainInv
public import ArtGallery.ETR.Ball

/-!
# ETR-INV is ∃ℝ-hard: the mathematical core (paper §4, Theorem 16 and Lemma 19)

`etrToINV φ` is the composition of

1. `ETR.Formula.toCircuit` (formula → ETR^{1,+,·} system on the variables `< N`,
   `N = φ.circuitVars`, with `m` equations),
2. `Gate.scaleSystem N k` with `k = ballExp N m + 2` (→ ETR^{1/8,+,·}; by the ball theorem
   `Gate.ball_bound` the scaled solution lies in `[-1/8, 1/8]`),
3. `Chain.invSystem` (→ ETR-INV, via `X = x + 7/8`).

Main results:

* `etrToINV_vars`: all indices are below `etrToINVVars φ`;
* `etrToINV_complete`: if `φ` is satisfiable, the ETR-INV instance has a solution in `[1/2, 2]`;
* `etrToINV_sound`: every solution `y` of the instance (without range restriction) comes from a
  satisfying assignment `x` of `φ` by the affine map `y i = ε x i + 7/8` on the original
  variables (`ε = etrScale φ`), as in Lemma 19 of the paper;
* `etrScale_pos`: `0 < ε`;
* `etrToINV_iff`: `φ` is satisfiable iff the instance is.
-/

@[expose] public section

namespace ArtGallery

open ArtGallery.Gate ArtGallery.Chain

/-- The exponent `k = E + 2`, where `2^(2^E)` is the radius of the ball theorem for the system
`φ.toCircuit`. -/
def etrK (φ : ETR.Formula) : ℕ := ballExp φ.circuitVars φ.toCircuit.length + 2

/-- The scaling factor `ε = 2^(-2^k)`. -/
def etrScale (φ : ETR.Formula) : ℚ := (1 / 2 : ℚ) ^ 2 ^ etrK φ

/-- The number of variables of the ETR^{1/8,+,·} system. -/
def etrScaledVars (φ : ETR.Formula) : ℕ := φ.circuitVars + etrK φ + 1 + φ.toCircuit.length

/-- The ETR^{1/8,+,·} system of `φ`. -/
def etrScaled (φ : ETR.Formula) : List Gate := scaleSystem φ.circuitVars (etrK φ) φ.toCircuit

/-- **The ETR-INV instance of a formula.** -/
def etrToINV (φ : ETR.Formula) : List ETRINV.Constraint := invSystem (etrScaledVars φ) (etrScaled φ)

/-- An exclusive bound on the variable indices of `etrToINV φ`. -/
def etrToINVVars (φ : ETR.Formula) : ℕ := etrScaledVars φ + 7 + 35 * (etrScaled φ).length

theorem etrK_two_le (φ : ETR.Formula) : 2 ≤ etrK φ := by
  simp only [etrK]
  omega

theorem etrScale_pos (φ : ETR.Formula) : 0 < etrScale φ := by
  simp only [etrScale]
  positivity

theorem etrScale_cast (φ : ETR.Formula) : (etrScale φ : ℝ) = (1 / 2 : ℝ) ^ 2 ^ etrK φ := by
  simp only [etrScale]
  push_cast
  ring

theorem etrScaled_vars (φ : ETR.Formula) : ∀ g ∈ etrScaled φ, g.VarsLt (etrScaledVars φ) :=
  scaleSystem_vars (etrK_two_le φ) φ.toCircuit_vars

/-- All variable indices of `etrToINV φ` are below `etrToINVVars φ`. -/
theorem etrToINV_vars (φ : ETR.Formula) : ∀ c ∈ etrToINV φ, c.VarsLt (etrToINVVars φ) :=
  invSystem_vars (etrScaled_vars φ)

/-- **Completeness**: if `φ` is satisfiable, then `etrToINV φ` has a solution in `[1/2, 2]`. -/
theorem etrToINV_complete (φ : ETR.Formula) (h : φ.Satisfiable) :
    ETRINV.Satisfiable (etrToINV φ) := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨v, hv, -⟩ := φ.toCircuit_complete x hx
  obtain ⟨w, hw, hwR⟩ := ball_bound φ.toCircuit φ.circuitVars φ.toCircuit_vars ⟨v, hv⟩
  obtain ⟨y, hy, hyr⟩ := scaleSystem_complete (etrK_two_le φ) φ.toCircuit_vars hw hwR
    (eps_mul_ball_le _)
  obtain ⟨Y, hYr, hY, -, -⟩ := invSystem_complete (etrScaled_vars φ) hy hyr
  exact ⟨Y, hYr, hY⟩

/-- **Soundness** (the affine correspondence of Lemma 19): every solution `y` of `etrToINV φ`,
with no range restriction, comes from a satisfying assignment `x` of `φ` via
`y i = ε x i + 7/8` on the variables of `φ`. -/
theorem etrToINV_sound (φ : ETR.Formula) (y : ℕ → ℝ)
    (hy : ∀ c ∈ etrToINV φ, c.Holds y) :
    ∃ x : ℕ → ℝ, φ.Holds x ∧ ∀ i < φ.varBound, y i = (etrScale φ : ℝ) * x i + 7 / 8 := by
  have h₁ := invSystem_sound hy
  have h₂ := scaleSystem_sound (etrK_two_le φ) φ.toCircuit h₁
  refine ⟨_, φ.toCircuit_sound _ h₂, fun i _ => ?_⟩
  rw [etrScale_cast]
  have hε : (0 : ℝ) < (1 / 2) ^ 2 ^ etrK φ := by positivity
  field_simp
  ring

/-- `φ` is satisfiable iff its ETR-INV instance is. -/
theorem etrToINV_iff (φ : ETR.Formula) : φ.Satisfiable ↔ ETRINV.Satisfiable (etrToINV φ) := by
  refine ⟨etrToINV_complete φ, fun ⟨y, _, hy⟩ => ?_⟩
  obtain ⟨x, hx, -⟩ := etrToINV_sound φ y hy
  exact ⟨x, hx⟩

end ArtGallery

end
