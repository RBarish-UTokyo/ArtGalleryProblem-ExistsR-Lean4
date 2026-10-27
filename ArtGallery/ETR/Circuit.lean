module

public import ArtGallery.ETR.Gate
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# From ETR formulas to ETR^{1,+,·} systems: syntax

This file and `ArtGallery.ETR.CircuitSem` translate a quantifier-free formula of the existential
theory of the reals into a system of equations `x = 1`, `x + y = z`, `x · y = z` (the analogue of
the paper's Lemma 17 and of the paragraph "Reduction to ETR^{1,+,·}").

* `ETR.Formula.varBound`: an exclusive bound on the variable indices of a formula.
* `ETR.Formula.nnf`: the negation normal forms (`ETR.NNF`) of `φ` and of `¬φ`, computed
  simultaneously by one structural recursion.
* `Circuit.Comp`: a compiled subterm or subformula: a list of gates over the variables
  `inl i` (the original variable `x i`) and `inr j` (the `j`-th auxiliary variable), a result
  variable and the number of auxiliary variables used.  Compilation is bottom-up
  (`ETR.Term.comp`, `ETR.NNF.comp`): the auxiliary variables of the second argument of a binary
  node are shifted by the number used by the first one.
* A term compiles to a circuit whose result variable carries the value of the term.  A formula
  `ψ` compiles to a circuit with a *residual* variable `r` such that `r = 0` is satisfiable
  (over the auxiliary variables) exactly when `ψ` holds:
  `s = t ↦ r = s − t`, `s ≤ t ↦ r = (t − s) − σ²`, `s < t ↦ r = (t − s) σ² − 1`,
  `ψ₁ ∧ ψ₂ ↦ r = r₁² + r₂²`, `ψ₁ ∨ ψ₂ ↦ r = r₁ r₂`.
* `ETR.Formula.toCircuit`: the final system, with the auxiliary variable `j` placed at index
  `φ.varBound + j` and the equations `z + z = z`, `r + z = z` added.
-/

@[expose] public section

namespace ArtGallery

namespace ETR

/-! ## Variable bounds -/

/-- An exclusive upper bound on the variable indices of a term (one more than the largest). -/
def Term.varBound : Term → ℕ
  | .var i => i + 1
  | .zero => 0
  | .one => 0
  | .add s t => max s.varBound t.varBound
  | .sub s t => max s.varBound t.varBound
  | .mul s t => max s.varBound t.varBound

/-- An exclusive upper bound on the variable indices of a formula (one more than the largest). -/
def Formula.varBound : Formula → ℕ
  | .eq s t => max s.varBound t.varBound
  | .lt s t => max s.varBound t.varBound
  | .le s t => max s.varBound t.varBound
  | .not φ => φ.varBound
  | .and φ ψ => max φ.varBound ψ.varBound
  | .or φ ψ => max φ.varBound ψ.varBound

theorem Term.varsLt_mono {n m : ℕ} (h : n ≤ m) (t : Term) (ht : t.VarsLt n) : t.VarsLt m := by
  induction t with
  | var i => exact lt_of_lt_of_le ht h
  | zero => trivial
  | one => trivial
  | add s t ihs iht => obtain ⟨h₁, h₂⟩ := ht; exact And.intro (ihs h₁) (iht h₂)
  | sub s t ihs iht => obtain ⟨h₁, h₂⟩ := ht; exact And.intro (ihs h₁) (iht h₂)
  | mul s t ihs iht => obtain ⟨h₁, h₂⟩ := ht; exact And.intro (ihs h₁) (iht h₂)

/-- The variables of a term are below its `varBound`. -/
theorem Term.varsLt_varBound (t : Term) : t.VarsLt t.varBound := by
  induction t with
  | var i => exact Nat.lt_succ_self i
  | zero => trivial
  | one => trivial
  | add s t ihs iht =>
    exact And.intro (varsLt_mono (le_max_left _ _) s ihs) (varsLt_mono (le_max_right _ _) t iht)
  | sub s t ihs iht =>
    exact And.intro (varsLt_mono (le_max_left _ _) s ihs) (varsLt_mono (le_max_right _ _) t iht)
  | mul s t ihs iht =>
    exact And.intro (varsLt_mono (le_max_left _ _) s ihs) (varsLt_mono (le_max_right _ _) t iht)

theorem Formula.varsLt_mono {n m : ℕ} (h : n ≤ m) (φ : Formula) (hφ : φ.VarsLt n) :
    φ.VarsLt m := by
  induction φ with
  | eq s t => obtain ⟨h₁, h₂⟩ := hφ; exact And.intro (s.varsLt_mono h h₁) (t.varsLt_mono h h₂)
  | lt s t => obtain ⟨h₁, h₂⟩ := hφ; exact And.intro (s.varsLt_mono h h₁) (t.varsLt_mono h h₂)
  | le s t => obtain ⟨h₁, h₂⟩ := hφ; exact And.intro (s.varsLt_mono h h₁) (t.varsLt_mono h h₂)
  | not φ ih => exact ih hφ
  | and φ ψ ih₁ ih₂ => obtain ⟨h₁, h₂⟩ := hφ; exact And.intro (ih₁ h₁) (ih₂ h₂)
  | or φ ψ ih₁ ih₂ => obtain ⟨h₁, h₂⟩ := hφ; exact And.intro (ih₁ h₁) (ih₂ h₂)

/-- The variables of a formula are below its `varBound`. -/
theorem Formula.varsLt_varBound (φ : Formula) : φ.VarsLt φ.varBound := by
  induction φ with
  | eq s t =>
    exact And.intro (s.varsLt_mono (le_max_left _ _) s.varsLt_varBound)
      (t.varsLt_mono (le_max_right _ _) t.varsLt_varBound)
  | lt s t =>
    exact And.intro (s.varsLt_mono (le_max_left _ _) s.varsLt_varBound)
      (t.varsLt_mono (le_max_right _ _) t.varsLt_varBound)
  | le s t =>
    exact And.intro (s.varsLt_mono (le_max_left _ _) s.varsLt_varBound)
      (t.varsLt_mono (le_max_right _ _) t.varsLt_varBound)
  | not φ ih => exact ih
  | and φ ψ ih₁ ih₂ =>
    exact And.intro (varsLt_mono (le_max_left _ _) φ ih₁) (varsLt_mono (le_max_right _ _) ψ ih₂)
  | or φ ψ ih₁ ih₂ =>
    exact And.intro (varsLt_mono (le_max_left _ _) φ ih₁) (varsLt_mono (le_max_right _ _) ψ ih₂)

/-! ## Negation normal form -/

/-- Formulas in negation normal form: atoms `=, <, ≤`, closed under `∧, ∨`. -/
inductive NNF where
  | eq (s t : Term)
  | lt (s t : Term)
  | le (s t : Term)
  | and (φ ψ : NNF)
  | or (φ ψ : NNF)

/-- The formula in negation normal form holds under the assignment `x`. -/
def NNF.Holds (x : ℕ → ℝ) : NNF → Prop
  | .eq s t => s.eval x = t.eval x
  | .lt s t => s.eval x < t.eval x
  | .le s t => s.eval x ≤ t.eval x
  | .and φ ψ => φ.Holds x ∧ ψ.Holds x
  | .or φ ψ => φ.Holds x ∨ ψ.Holds x

/-- Every variable of the formula in negation normal form has index less than `n`. -/
def NNF.VarsLt (n : ℕ) : NNF → Prop
  | .eq s t => s.VarsLt n ∧ t.VarsLt n
  | .lt s t => s.VarsLt n ∧ t.VarsLt n
  | .le s t => s.VarsLt n ∧ t.VarsLt n
  | .and φ ψ => φ.VarsLt n ∧ ψ.VarsLt n
  | .or φ ψ => φ.VarsLt n ∧ ψ.VarsLt n

/-- The negation normal forms of `φ` and of `¬ φ`, computed together by pushing negations to the
atoms (`¬(s = t) ⇒ s < t ∨ t < s`, `¬(s < t) ⇒ t ≤ s`, `¬(s ≤ t) ⇒ t < s`, De Morgan). -/
def Formula.nnf : Formula → NNF × NNF
  | .eq s t => (.eq s t, .or (.lt s t) (.lt t s))
  | .lt s t => (.lt s t, .le t s)
  | .le s t => (.le s t, .lt t s)
  | .not φ => φ.nnf.swap
  | .and φ ψ =>
    let p := φ.nnf
    let q := ψ.nnf
    (.and p.1 q.1, .or p.2 q.2)
  | .or φ ψ =>
    let p := φ.nnf
    let q := ψ.nnf
    (.or p.1 q.1, .and p.2 q.2)

/-- The negation normal forms are equivalent to `φ` and `¬ φ`. -/
theorem Formula.nnf_holds (x : ℕ → ℝ) (φ : Formula) :
    (φ.nnf.1.Holds x ↔ φ.Holds x) ∧ (φ.nnf.2.Holds x ↔ ¬ φ.Holds x) := by
  induction φ with
  | eq s t =>
    refine ⟨Iff.rfl, ?_⟩
    show (s.eval x < t.eval x ∨ t.eval x < s.eval x) ↔ ¬ s.eval x = t.eval x
    constructor
    · rintro (h | h) he <;> linarith
    · exact lt_or_gt_of_ne
  | lt s t =>
    refine ⟨Iff.rfl, ?_⟩
    show t.eval x ≤ s.eval x ↔ ¬ s.eval x < t.eval x
    exact not_lt.symm
  | le s t =>
    refine ⟨Iff.rfl, ?_⟩
    show t.eval x < s.eval x ↔ ¬ s.eval x ≤ t.eval x
    exact not_le.symm
  | not φ ih =>
    show (φ.nnf.2.Holds x ↔ ¬ φ.Holds x) ∧ (φ.nnf.1.Holds x ↔ ¬ ¬ φ.Holds x)
    exact ⟨ih.2, ih.1.trans not_not.symm⟩
  | and φ ψ ih₁ ih₂ =>
    show (φ.nnf.1.Holds x ∧ ψ.nnf.1.Holds x ↔ φ.Holds x ∧ ψ.Holds x) ∧
      (φ.nnf.2.Holds x ∨ ψ.nnf.2.Holds x ↔ ¬ (φ.Holds x ∧ ψ.Holds x))
    rw [ih₁.1, ih₂.1, ih₁.2, ih₂.2]
    exact ⟨Iff.rfl, not_and_or.symm⟩
  | or φ ψ ih₁ ih₂ =>
    show (φ.nnf.1.Holds x ∨ ψ.nnf.1.Holds x ↔ φ.Holds x ∨ ψ.Holds x) ∧
      (φ.nnf.2.Holds x ∧ ψ.nnf.2.Holds x ↔ ¬ (φ.Holds x ∨ ψ.Holds x))
    rw [ih₁.1, ih₂.1, ih₁.2, ih₂.2]
    exact ⟨Iff.rfl, not_or.symm⟩

/-- The negation normal forms have the same variables. -/
theorem Formula.nnf_varsLt {n : ℕ} (φ : Formula) (h : φ.VarsLt n) :
    φ.nnf.1.VarsLt n ∧ φ.nnf.2.VarsLt n := by
  induction φ with
  | eq s t =>
    obtain ⟨h₁, h₂⟩ := h
    exact ⟨⟨h₁, h₂⟩, ⟨⟨h₁, h₂⟩, ⟨h₂, h₁⟩⟩⟩
  | lt s t =>
    obtain ⟨h₁, h₂⟩ := h
    exact ⟨⟨h₁, h₂⟩, ⟨h₂, h₁⟩⟩
  | le s t =>
    obtain ⟨h₁, h₂⟩ := h
    exact ⟨⟨h₁, h₂⟩, ⟨h₂, h₁⟩⟩
  | not φ ih =>
    obtain ⟨h₁, h₂⟩ := ih h
    exact ⟨h₂, h₁⟩
  | and φ ψ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := h
    obtain ⟨a₁, b₁⟩ := ih₁ h₁
    obtain ⟨a₂, b₂⟩ := ih₂ h₂
    exact ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩
  | or φ ψ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := h
    obtain ⟨a₁, b₁⟩ := ih₁ h₁
    obtain ⟨a₂, b₂⟩ := ih₂ h₂
    exact ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩

end ETR

/-! ## Gates over original and auxiliary variables -/

namespace Circuit

open ArtGallery.Gate

/-- Circuit variables: `inl i` is the original variable `x i`, `inr j` the `j`-th auxiliary
variable. -/
abbrev CVar : Type := ℕ ⊕ ℕ

/-- An equation `x = 1`, `x + y = z` or `x · y = z` on circuit variables. -/
inductive CGate where
  | one (x : CVar)
  | add (x y z : CVar)
  | mul (x y z : CVar)

/-- The equation holds under the valuation `ρ`. -/
def CGate.Holds (ρ : CVar → ℝ) : CGate → Prop
  | .one x => ρ x = 1
  | .add x y z => ρ x + ρ y = ρ z
  | .mul x y z => ρ x * ρ y = ρ z

/-- Every variable of the equation satisfies `P`. -/
def CGate.All (P : CVar → Prop) : CGate → Prop
  | .one x => P x
  | .add x y z => P x ∧ P y ∧ P z
  | .mul x y z => P x ∧ P y ∧ P z

/-- Shift auxiliary variables by `k`. -/
def shiftVar (k : ℕ) : CVar → CVar
  | .inl i => .inl i
  | .inr j => .inr (j + k)

/-- Shift the auxiliary variables of an equation by `k`. -/
def CGate.shift (k : ℕ) : CGate → CGate
  | .one x => .one (shiftVar k x)
  | .add x y z => .add (shiftVar k x) (shiftVar k y) (shiftVar k z)
  | .mul x y z => .mul (shiftVar k x) (shiftVar k y) (shiftVar k z)

/-- The final index of a circuit variable: original variables keep their index, auxiliary
variable `j` goes to `n + j`. -/
def place (n : ℕ) : CVar → ℕ
  | .inl i => i
  | .inr j => n + j

/-- The equation on final indices. -/
def CGate.toGate (n : ℕ) : CGate → Gate
  | .one x => .one (place n x)
  | .add x y z => .add (place n x) (place n y) (place n z)
  | .mul x y z => .mul (place n x) (place n y) (place n z)

/-- The variable is original, or auxiliary with index below `c`. -/
def FLt (c : ℕ) : CVar → Prop
  | .inl _ => True
  | .inr j => j < c

/-- The variable is auxiliary, or original with index below `n`. -/
def OLt (n : ℕ) : CVar → Prop
  | .inl i => i < n
  | .inr _ => True

theorem FLt.mono {m n : ℕ} (h : m ≤ n) : ∀ {v : CVar}, FLt m v → FLt n v
  | .inl _, _ => trivial
  | .inr _, hv => lt_of_lt_of_le hv h

theorem CGate.All.mono {P Q : CVar → Prop} (h : ∀ v, P v → Q v) :
    ∀ {g : CGate}, g.All P → g.All Q
  | .one x, hx => h x hx
  | .add x y z, ⟨hx, hy, hz⟩ => ⟨h x hx, h y hy, h z hz⟩
  | .mul x y z, ⟨hx, hy, hz⟩ => ⟨h x hx, h y hy, h z hz⟩

theorem CGate.All.and {P Q : CVar → Prop} :
    ∀ {g : CGate}, g.All P → g.All Q → g.All (fun v => P v ∧ Q v)
  | .one _, hx, h'x => ⟨hx, h'x⟩
  | .add _ _ _, ⟨hx, hy, hz⟩, ⟨h'x, h'y, h'z⟩ => ⟨⟨hx, h'x⟩, ⟨hy, h'y⟩, ⟨hz, h'z⟩⟩
  | .mul _ _ _, ⟨hx, hy, hz⟩, ⟨h'x, h'y, h'z⟩ => ⟨⟨hx, h'x⟩, ⟨hy, h'y⟩, ⟨hz, h'z⟩⟩

theorem CGate.all_shift {P Q : CVar → Prop} (k : ℕ) (h : ∀ v, P v → Q (shiftVar k v)) :
    ∀ {g : CGate}, g.All P → (g.shift k).All Q
  | .one x, hx => h x hx
  | .add x y z, ⟨hx, hy, hz⟩ => ⟨h x hx, h y hy, h z hz⟩
  | .mul x y z, ⟨hx, hy, hz⟩ => ⟨h x hx, h y hy, h z hz⟩

/-- Whether an equation holds depends only on the values of its variables. -/
theorem CGate.holds_congr {ρ ρ' : CVar → ℝ} {P : CVar → Prop} (h : ∀ v, P v → ρ v = ρ' v) :
    ∀ {g : CGate}, g.All P → (g.Holds ρ ↔ g.Holds ρ')
  | .one x, hx => by simp only [CGate.Holds, h x hx]
  | .add x y z, ⟨hx, hy, hz⟩ => by simp only [CGate.Holds, h x hx, h y hy, h z hz]
  | .mul x y z, ⟨hx, hy, hz⟩ => by simp only [CGate.Holds, h x hx, h y hy, h z hz]

theorem elim_shiftVar (x a : ℕ → ℝ) (k : ℕ) (v : CVar) :
    Sum.elim x a (shiftVar k v) = Sum.elim x (fun j => a (j + k)) v := by
  cases v <;> rfl

theorem CGate.holds_shift (x a : ℕ → ℝ) (k : ℕ) (g : CGate) :
    (g.shift k).Holds (Sum.elim x a) ↔ g.Holds (Sum.elim x (fun j => a (j + k))) := by
  cases g <;> simp only [CGate.shift, CGate.Holds, elim_shiftVar]

theorem CGate.holds_toGate (n : ℕ) (v : ℕ → ℝ) (g : CGate) :
    (g.toGate n).Holds v ↔ g.Holds (fun w => v (place n w)) := by
  cases g <;> exact Iff.rfl

theorem CGate.varsLt_toGate {n N : ℕ} {g : CGate} (h : g.All (fun w => place n w < N)) :
    (g.toGate n).VarsLt N := by
  cases g <;> exact h

/-! ## Compiled subterms and subformulas -/

/-- A compiled subterm or subformula: its equations, its result (value or residual) variable,
and the number `cnt` of auxiliary variables it uses (`inr 0, …, inr (cnt - 1)`). -/
structure Comp where
  /-- The equations. -/
  gates : List CGate
  /-- The result variable. -/
  res : CVar
  /-- The number of auxiliary variables. -/
  cnt : ℕ

/-- The equations of `c` followed by those of `d`, whose auxiliary variables are shifted by
`c.cnt`. -/
def Comp.pair (c d : Comp) : List CGate := c.gates ++ d.gates.map (CGate.shift c.cnt)

/-- Combine `c` and `d` with `k` new auxiliary variables (`inr (c.cnt + d.cnt + i)`, `i < k`),
new equations `new` and result `res`. -/
def Comp.ext (c d : Comp) (new : List CGate) (res : CVar) (k : ℕ) : Comp :=
  ⟨c.pair d ++ new, res, c.cnt + d.cnt + k⟩

/-- `s + t`. -/
def Comp.addC (c d : Comp) : Comp :=
  c.ext d [.add c.res (shiftVar c.cnt d.res) (.inr (c.cnt + d.cnt))] (.inr (c.cnt + d.cnt)) 1

/-- `s − t` (the new variable `w` satisfies `w + t = s`); also the residual of `s = t`. -/
def Comp.subC (c d : Comp) : Comp :=
  c.ext d [.add (.inr (c.cnt + d.cnt)) (shiftVar c.cnt d.res) c.res] (.inr (c.cnt + d.cnt)) 1

/-- `s · t`. -/
def Comp.mulC (c d : Comp) : Comp :=
  c.ext d [.mul c.res (shiftVar c.cnt d.res) (.inr (c.cnt + d.cnt))] (.inr (c.cnt + d.cnt)) 1

/-- The residual of `s ≤ t`: `σ`, `q = σ·σ`, `d = t − s`, `r = d − q`. -/
def Comp.leC (c d : Comp) : Comp :=
  let f := c.cnt + d.cnt
  c.ext d [.mul (.inr f) (.inr f) (.inr (f + 1)), .add (.inr (f + 2)) c.res (shiftVar c.cnt d.res),
    .add (.inr (f + 3)) (.inr (f + 1)) (.inr (f + 2))] (.inr (f + 3)) 4

/-- The residual of `s < t`: `σ`, `q = σ·σ`, `d = t − s`, `p = d·q`, `o = 1`, `r = p − o`. -/
def Comp.ltC (c d : Comp) : Comp :=
  let f := c.cnt + d.cnt
  c.ext d [.mul (.inr f) (.inr f) (.inr (f + 1)), .add (.inr (f + 2)) c.res (shiftVar c.cnt d.res),
    .mul (.inr (f + 2)) (.inr (f + 1)) (.inr (f + 3)), .one (.inr (f + 4)),
    .add (.inr (f + 5)) (.inr (f + 4)) (.inr (f + 3))] (.inr (f + 5)) 6

/-- The residual of a conjunction: `r₁·r₁ + r₂·r₂`. -/
def Comp.andC (c d : Comp) : Comp :=
  let f := c.cnt + d.cnt
  c.ext d [.mul c.res c.res (.inr f), .mul (shiftVar c.cnt d.res) (shiftVar c.cnt d.res)
    (.inr (f + 1)), .add (.inr f) (.inr (f + 1)) (.inr (f + 2))] (.inr (f + 2)) 3

/-- The residual of a disjunction: `r₁·r₂`. -/
def Comp.orC (c d : Comp) : Comp :=
  c.ext d [.mul c.res (shiftVar c.cnt d.res) (.inr (c.cnt + d.cnt))] (.inr (c.cnt + d.cnt)) 1

end Circuit

namespace ETR

open Circuit

/-- Bottom-up compilation of a term. -/
def Term.comp : Term → Comp
  | .var i => ⟨[], .inl i, 0⟩
  | .zero => ⟨[.add (.inr 0) (.inr 0) (.inr 0)], .inr 0, 1⟩
  | .one => ⟨[.one (.inr 0)], .inr 0, 1⟩
  | .add s t => Comp.addC s.comp t.comp
  | .sub s t => Comp.subC s.comp t.comp
  | .mul s t => Comp.mulC s.comp t.comp

/-- Bottom-up compilation of a formula in negation normal form (result: the residual). -/
def NNF.comp : NNF → Comp
  | .eq s t => Comp.subC s.comp t.comp
  | .lt s t => Comp.ltC s.comp t.comp
  | .le s t => Comp.leC s.comp t.comp
  | .and φ ψ => Comp.andC φ.comp ψ.comp
  | .or φ ψ => Comp.orC φ.comp ψ.comp

/-- The compiled positive normal form of `φ`. -/
def Formula.compiled (φ : Formula) : Comp := φ.nnf.1.comp

/-- **The ETR^{1,+,·} system of a formula.**  The auxiliary variable `j` gets index
`φ.varBound + j`; the extra auxiliary variable `z` (index `cnt`) satisfies `z + z = z`, and the
residual `r` satisfies `r + z = z`. -/
def Formula.toCircuit (φ : Formula) : List Gate.Gate :=
  let c := φ.compiled
  (c.gates ++ [CGate.add (.inr c.cnt) (.inr c.cnt) (.inr c.cnt),
    CGate.add c.res (.inr c.cnt) (.inr c.cnt)]).map (CGate.toGate φ.varBound)

/-- An exclusive bound on the variable indices of `φ.toCircuit`. -/
def Formula.circuitVars (φ : Formula) : ℕ := φ.varBound + (φ.compiled.cnt + 1)

end ETR

end ArtGallery

end
