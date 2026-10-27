module

public import ArtGallery.PTime.ETRDecode
public import ArtGallery.PTime.INVCode
public import ArtGallery.PTime.Classes

/-!
# ETR-INV is in `∃ℝ`

`ETRINV.invToETR Φ` is the conjunction of the equations of `Φ` (as ETR atoms) and of the range
conditions `1 ≤ x + x`, `x ≤ 1 + 1` for every variable `x i` with `i < ETRINV.varBound Φ` (an
explicit bound on the variable indices).  Unused variables are free; they are set to `1`.

* `ETRINV.invToETR_satisfiable : (invToETR Φ).Satisfiable ↔ ETRINV.Satisfiable Φ`;
* `PT.invToETR`, and the reduction `ETRINV.invReduction` (decode, translate, encode; a
  non-code goes to `falseFormula`) is polynomial-time (`PT.invReduction`);
* **`ArtGallery.etrinv_inER : InER ETRINV`**.

Also: `ETR.conj` (the conjunction of a list of formulas) with `ETR.conj_holds`, `PT.conj`, and
`ETR.ETR_encode_iff : ETR φ.encode ↔ φ.Satisfiable`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery

open Complexity Complexity.PT Complexity.PT.Code

namespace ETR

/-- The conjunction of a list of formulas (`trueFormula` for the empty list). -/
def conj : List Formula → Formula
  | [] => trueFormula
  | φ :: l => .and φ (conj l)

theorem conj_holds (x : ℕ → ℝ) (l : List Formula) : (conj l).Holds x ↔ ∀ φ ∈ l, φ.Holds x := by
  induction l with
  | nil => simp [conj, trueFormula, Formula.Holds, Term.eval]
  | cons φ l ih => simp [conj, Formula.Holds, ih]

theorem conj_toks (l : List Formula) :
    (conj l).toks = l.flatMap (fun φ => 4 :: φ.toks) ++ trueFormula.toks := by
  induction l with
  | nil => rfl
  | cons φ l ih => simp [conj, Formula.toks, ih]

/-- Membership of a code in `ETR`. -/
theorem ETR_encode_iff (φ : Formula) : ArtGallery.ETR φ.encode ↔ φ.Satisfiable :=
  ⟨fun ⟨_, h, hs⟩ => Formula.encode_injective h ▸ hs, fun h => ⟨φ, rfl, h⟩⟩

theorem falseFormula_not_satisfiable : ¬ falseFormula.Satisfiable := by
  rintro ⟨x, hx⟩
  simp [falseFormula, Formula.Holds, Term.eval] at hx
  linarith

end ETR

open ETR

/-- The conjunction of a list of formulas is polynomial-time. -/
@[fun_prop] protected theorem PT.conj {α : Type} [Code α] {l : α → List Formula} (hl : PT l) :
    PT (fun a => conj (l a)) := by
  refine PT.formula_of_toks ?_
  have h : PT (fun a => (l a).flatMap (fun φ => 4 :: φ.toks) ++ trueFormula.toks) := by
    fun_prop
  exact h.of_eq fun a => (conj_toks (l a)).symm

namespace ETRINV

/-- The ETR atom of an equation. -/
def Constraint.toFormula : Constraint → Formula
  | .one x => .eq (.var x) .one
  | .add x y z => .eq (.add (.var x) (.var y)) (.var z)
  | .inv x y => .eq (.mul (.var x) (.var y)) .one

/-- A bound on the variable indices of an equation. -/
def Constraint.varBound : Constraint → ℕ
  | .one x => x + 1
  | .add x y z => x + y + z + 1
  | .inv x y => x + y + 1

/-- A bound on the variable indices of an instance. -/
def varBound (Φ : List Constraint) : ℕ := (Φ.map Constraint.varBound).sum

/-- The range condition `1 ≤ x + x ∧ x ≤ 1 + 1`, i.e. `x ∈ [1/2, 2]`. -/
def rangeFormula (i : ℕ) : Formula :=
  .and (.le .one (.add (.var i) (.var i))) (.le (.var i) (.add .one .one))

/-- **The translation of ETR-INV into ETR.** -/
def invToETR (Φ : List Constraint) : Formula :=
  conj (Φ.map Constraint.toFormula ++ (List.range (varBound Φ)).map rangeFormula)

theorem Constraint.toFormula_holds (x : ℕ → ℝ) (c : Constraint) :
    c.toFormula.Holds x ↔ c.Holds x := by
  cases c <;> simp [Constraint.toFormula, Formula.Holds, Term.eval, Constraint.Holds]

theorem rangeFormula_holds (x : ℕ → ℝ) (i : ℕ) :
    (rangeFormula i).Holds x ↔ 1 / 2 ≤ x i ∧ x i ≤ 2 := by
  simp only [rangeFormula, Formula.Holds, Term.eval]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

theorem le_sum_of_mem' {a : ℕ} {l : List ℕ} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := ih h
      simp only [List.sum_cons]
      omega

theorem Constraint.varBound_le {c : Constraint} {Φ : List Constraint} (h : c ∈ Φ) :
    c.varBound ≤ ETRINV.varBound Φ :=
  le_sum_of_mem' (List.mem_map_of_mem h)

/-- An equation only depends on the variables below its bound. -/
theorem Constraint.holds_congr (c : Constraint) {x v : ℕ → ℝ} {N : ℕ} (hN : c.varBound ≤ N)
    (hxv : ∀ i < N, x i = v i) : c.Holds x ↔ c.Holds v := by
  cases c with
  | one a =>
    simp only [Constraint.varBound] at hN
    simp only [Constraint.Holds, hxv a (by omega)]
  | add a b d =>
    simp only [Constraint.varBound] at hN
    simp only [Constraint.Holds, hxv a (by omega), hxv b (by omega), hxv d (by omega)]
  | inv a b =>
    simp only [Constraint.varBound] at hN
    simp only [Constraint.Holds, hxv a (by omega), hxv b (by omega)]

theorem invToETR_holds (x : ℕ → ℝ) (Φ : List Constraint) :
    (invToETR Φ).Holds x ↔ (∀ c ∈ Φ, c.Holds x) ∧ ∀ i < varBound Φ, 1 / 2 ≤ x i ∧ x i ≤ 2 := by
  simp [invToETR, conj_holds, Constraint.toFormula_holds, rangeFormula_holds, or_imp,
    forall_and]

/-- **Correctness of the translation.** -/
theorem invToETR_satisfiable (Φ : List Constraint) :
    (invToETR Φ).Satisfiable ↔ Satisfiable Φ := by
  constructor
  · rintro ⟨x, hx⟩
    rw [invToETR_holds] at hx
    obtain ⟨hc, hr⟩ := hx
    refine ⟨fun i => if i < varBound Φ then x i else 1, fun i => ?_, fun c hcΦ => ?_⟩
    · by_cases hi : i < varBound Φ
      · simpa [hi] using hr i hi
      · simp only [hi, ite_false]; norm_num
    · refine (c.holds_congr (Constraint.varBound_le hcΦ) fun i hi => ?_).mp (hc c hcΦ)
      simp [hi]
  · rintro ⟨v, hv, hc⟩
    exact ⟨v, (invToETR_holds v Φ).mpr ⟨hc, fun i _ => hv i⟩⟩

/-- **The reduction from ETR-INV to ETR** on raw words. -/
def invReduction (w : Word) : Word :=
  match decodeINV w with
  | some Φ => (invToETR Φ).encode
  | none => falseFormula.encode

theorem invReduction_correct (w : Word) : ArtGallery.ETRINV w ↔ ArtGallery.ETR (invReduction w) := by
  unfold invReduction
  cases h : decodeINV w with
  | none =>
    simp only
    constructor
    · rintro ⟨Φ, rfl, _⟩
      rw [decodeINV_encode] at h
      exact absurd h (by simp)
    · intro h'
      exact absurd ((ETR_encode_iff _).mp h') falseFormula_not_satisfiable
  | some Φ =>
    simp only
    rw [← encode_of_decodeINV h, ETRINV_encode_iff, ETR_encode_iff, invToETR_satisfiable]

end ETRINV

open ETRINV

variable {α : Type} [Code α]

@[fun_prop] protected theorem PT.constraintToFormula {c : α → Constraint} (hc : PT c) :
    PT (fun a => (c a).toFormula) := by
  have h : PT (fun a => (c a).elim (fun x => Formula.eq (.var x) .one)
      (fun x y z => Formula.eq (.add (.var x) (.var y)) (.var z))
      (fun x y => Formula.eq (.mul (.var x) (.var y)) .one)) :=
    PT.constraintElim (f₁ := fun _ x => Formula.eq (.var x) .one)
      (f₂ := fun _ x y z => Formula.eq (.add (.var x) (.var y)) (.var z))
      (f₃ := fun _ x y => Formula.eq (.mul (.var x) (.var y)) .one)
      (by fun_prop) (by fun_prop) (by fun_prop) hc
  exact h.of_eq fun a => by cases c a <;> rfl

@[fun_prop] protected theorem PT.constraintVarBound {c : α → Constraint} (hc : PT c) :
    PT (fun a => (c a).varBound) := by
  have h : PT (fun a => (c a).elim (fun x => x + 1) (fun x y z => x + y + z + 1)
      (fun x y => x + y + 1)) :=
    PT.constraintElim (f₁ := fun _ x => x + 1) (f₂ := fun _ x y z => x + y + z + 1)
      (f₃ := fun _ x y => x + y + 1) (by fun_prop) (by fun_prop) (by fun_prop) hc
  exact h.of_eq fun a => by cases c a <;> rfl

@[fun_prop] protected theorem PT.rangeFormula {i : α → ℕ} (hi : PT i) :
    PT (fun a => rangeFormula (i a)) := by
  unfold rangeFormula
  fun_prop

/-- The translation is polynomial-time. -/
@[fun_prop] protected theorem PT.invToETR {Φ : α → List Constraint} (hΦ : PT Φ) :
    PT (fun a => invToETR (Φ a)) := by
  unfold invToETR varBound
  fun_prop

/-- The reduction is polynomial-time. -/
protected theorem PT.invReduction : PT invReduction := by
  refine PT.of_optionCases (o := decodeINV) (d := fun _ => falseFormula.encode)
    (f := fun _ Φ => (invToETR Φ).encode) (PT.decodeINV PT.id) (PT.const _) (by fun_prop) ?_ ?_
  · intro w h; simp [invReduction, h]
  · intro w Φ h; simp [invReduction, h]

/-- **ETR-INV is in `∃ℝ`.** -/
theorem etrinv_inER : InER ETRINV :=
  PT.polyRed PT.invReduction invReduction_correct

end ArtGallery

end
