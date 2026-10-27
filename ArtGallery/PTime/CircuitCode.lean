module

public import ArtGallery.PTime.TreeRec
public import ArtGallery.ETR.CircuitSem

/-!
# Polynomial time of the circuit compilation

Codes for the syntax of `ArtGallery.ETR.Circuit` (`Circuit.CGate`, `Circuit.Comp`,
`Gate.Gate`), polynomial-time constructors and operations, and:

* `ETR.Formula.compPair`: the pair `(φ.nnf.1.comp, φ.nnf.2.comp)` as a catamorphism on `φ`
  (`ETR.Formula.compPair_eq`), polynomial-time by `PT.formulaCata` (`PT.compPair`);
* `PT.compiled`, `PT.formulaVarBound`, `PT.toCircuit`, `PT.circuitVars`.

The size bounds: a compiled subterm has at most `size t` gates and auxiliary variables, a
compiled subformula (positive or negative normal form) at most `11 * size ψ`
(`ETR.Term.comp_len_le`, `ETR.Formula.compPair_len_le`), its variables are bounded
(`Comp.WF`, `Comp.OrigLt`), hence its size is quadratic (`Circuit.size_comp_le`).
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery

open Complexity Complexity.PT Complexity.PT.Code

/-! ### Codes -/

namespace Circuit

/-- An equation on circuit variables as a sum. -/
def CGate.toSum : CGate → CVar ⊕ (CVar × CVar × CVar) ⊕ (CVar × CVar × CVar)
  | .one x => .inl x
  | .add x y z => .inr (.inl (x, y, z))
  | .mul x y z => .inr (.inr (x, y, z))

/-- The inverse of `CGate.toSum`. -/
def CGate.ofSum : CVar ⊕ (CVar × CVar × CVar) ⊕ (CVar × CVar × CVar) → CGate
  | .inl x => .one x
  | .inr (.inl (x, y, z)) => .add x y z
  | .inr (.inr (x, y, z)) => .mul x y z

theorem CGate.ofSum_toSum (g : CGate) : CGate.ofSum g.toSum = g := by cases g <;> rfl

/-- Equations on circuit variables are coded as sums. -/
instance instCodeCGate : Code CGate := Code.ofInj CGate.toSum CGate.ofSum CGate.ofSum_toSum

/-- A compiled piece as a triple. -/
def Comp.toProd (c : Comp) : List CGate × CVar × ℕ := (c.gates, c.res, c.cnt)

/-- The inverse of `Comp.toProd`. -/
def Comp.ofProd (p : List CGate × CVar × ℕ) : Comp := ⟨p.1, p.2.1, p.2.2⟩

/-- Compiled pieces are coded as triples. -/
instance instCodeComp : Code Comp := Code.ofInj Comp.toProd Comp.ofProd (fun _ => rfl)

/-- Case analysis on an equation on circuit variables. -/
def CGate.elim {β : Type} (f₁ : CVar → β) (f₂ f₃ : CVar → CVar → CVar → β) : CGate → β
  | .one x => f₁ x
  | .add x y z => f₂ x y z
  | .mul x y z => f₃ x y z

theorem CGate.elim_eq {β : Type} (f₁ : CVar → β) (f₂ f₃ : CVar → CVar → CVar → β) (g : CGate) :
    g.elim f₁ f₂ f₃ = Sum.elim f₁ (Sum.elim (fun q => f₂ q.1 q.2.1 q.2.2)
      (fun q => f₃ q.1 q.2.1 q.2.2)) g.toSum := by
  cases g <;> rfl

theorem size_cgate (g : CGate) : size g = size g.toSum := rfl

theorem size_comp (c : Comp) : size c = size c.gates + size c.res + size c.cnt := by
  show size (c.gates, c.res, c.cnt) = _
  simp only [size_prod]
  omega

end Circuit

namespace Gate

/-- An equation as a sum. -/
def Gate.toSum : Gate → ℕ ⊕ (ℕ × ℕ × ℕ) ⊕ (ℕ × ℕ × ℕ)
  | .one x => .inl x
  | .add x y z => .inr (.inl (x, y, z))
  | .mul x y z => .inr (.inr (x, y, z))

/-- The inverse of `Gate.toSum`. -/
def Gate.ofSum : ℕ ⊕ (ℕ × ℕ × ℕ) ⊕ (ℕ × ℕ × ℕ) → Gate
  | .inl x => .one x
  | .inr (.inl (x, y, z)) => .add x y z
  | .inr (.inr (x, y, z)) => .mul x y z

theorem Gate.ofSum_toSum (g : Gate) : Gate.ofSum g.toSum = g := by cases g <;> rfl

/-- Equations are coded as sums. -/
instance instCodeGate : Code Gate := Code.ofInj Gate.toSum Gate.ofSum Gate.ofSum_toSum

/-- Case analysis on an equation. -/
def Gate.elim {β : Type} (f₁ : ℕ → β) (f₂ f₃ : ℕ → ℕ → ℕ → β) : Gate → β
  | .one x => f₁ x
  | .add x y z => f₂ x y z
  | .mul x y z => f₃ x y z

theorem Gate.elim_eq {β : Type} (f₁ : ℕ → β) (f₂ f₃ : ℕ → ℕ → ℕ → β) (g : Gate) :
    g.elim f₁ f₂ f₃ = Sum.elim f₁ (Sum.elim (fun q => f₂ q.1 q.2.1 q.2.2)
      (fun q => f₃ q.1 q.2.1 q.2.2)) g.toSum := by
  cases g <;> rfl

end Gate

open Circuit Gate

/-! ### Polynomial-time constructors and operations -/

section PTLemmas

variable {α β : Type} [Code α] [Code β]

@[fun_prop] protected theorem PT.cgateToSum {g : α → CGate} (hg : PT g) :
    PT (fun a => (g a).toSum) :=
  (PT.ofInj_to CGate.toSum CGate.ofSum CGate.ofSum_toSum).comp hg

theorem PT.cgate_of_toSum {g : α → CGate} (h : PT (fun a => (g a).toSum)) : PT g :=
  PT.ofInj_mk CGate.toSum CGate.ofSum CGate.ofSum_toSum h

@[fun_prop] protected theorem PT.cgateOne {x : α → CVar} (hx : PT x) :
    PT (fun a => CGate.one (x a)) :=
  PT.cgate_of_toSum (by simp only [CGate.toSum]; fun_prop)

@[fun_prop] protected theorem PT.cgateAdd {x y z : α → CVar} (hx : PT x) (hy : PT y)
    (hz : PT z) : PT (fun a => CGate.add (x a) (y a) (z a)) :=
  PT.cgate_of_toSum (by simp only [CGate.toSum]; fun_prop)

@[fun_prop] protected theorem PT.cgateMul {x y z : α → CVar} (hx : PT x) (hy : PT y)
    (hz : PT z) : PT (fun a => CGate.mul (x a) (y a) (z a)) :=
  PT.cgate_of_toSum (by simp only [CGate.toSum]; fun_prop)

/-- Case analysis on an equation on circuit variables. -/
@[fun_prop] protected theorem PT.cgateElim {g : α → CGate} {f₁ : α → CVar → β}
    {f₂ f₃ : α → CVar → CVar → CVar → β}
    (h₁ : PT (fun p : α × CVar => f₁ p.1 p.2))
    (h₂ : PT (fun p : α × CVar × CVar × CVar => f₂ p.1 p.2.1 p.2.2.1 p.2.2.2))
    (h₃ : PT (fun p : α × CVar × CVar × CVar => f₃ p.1 p.2.1 p.2.2.1 p.2.2.2)) (hg : PT g) :
    PT (fun a => (g a).elim (f₁ a) (f₂ a) (f₃ a)) := by
  have h : PT (fun a => Sum.elim (f₁ a) (Sum.elim (fun q => f₂ a q.1 q.2.1 q.2.2)
      (fun q => f₃ a q.1 q.2.1 q.2.2)) (g a).toSum) :=
    PT.sumElim h₁ (PT.sumElim (h₂.comp (PT.pair (PT.fst (PT.fst PT.id)) (PT.snd PT.id)))
      (h₃.comp (PT.pair (PT.fst (PT.fst PT.id)) (PT.snd PT.id))) PT.snd') (PT.cgateToSum hg)
  exact h.of_eq fun a => (CGate.elim_eq _ _ _ (g a)).symm

@[fun_prop] protected theorem PT.gateToSum {g : α → Gate} (hg : PT g) :
    PT (fun a => (g a).toSum) :=
  (PT.ofInj_to Gate.toSum Gate.ofSum Gate.ofSum_toSum).comp hg

theorem PT.gate_of_toSum {g : α → Gate} (h : PT (fun a => (g a).toSum)) : PT g :=
  PT.ofInj_mk Gate.toSum Gate.ofSum Gate.ofSum_toSum h

@[fun_prop] protected theorem PT.gateOne {x : α → ℕ} (hx : PT x) :
    PT (fun a => Gate.one (x a)) :=
  PT.gate_of_toSum (by simp only [Gate.toSum]; fun_prop)

@[fun_prop] protected theorem PT.gateAdd {x y z : α → ℕ} (hx : PT x) (hy : PT y) (hz : PT z) :
    PT (fun a => Gate.add (x a) (y a) (z a)) :=
  PT.gate_of_toSum (by simp only [Gate.toSum]; fun_prop)

@[fun_prop] protected theorem PT.gateMul {x y z : α → ℕ} (hx : PT x) (hy : PT y) (hz : PT z) :
    PT (fun a => Gate.mul (x a) (y a) (z a)) :=
  PT.gate_of_toSum (by simp only [Gate.toSum]; fun_prop)

/-- Case analysis on an equation. -/
@[fun_prop] protected theorem PT.gateElim {g : α → Gate} {f₁ : α → ℕ → β}
    {f₂ f₃ : α → ℕ → ℕ → ℕ → β}
    (h₁ : PT (fun p : α × ℕ => f₁ p.1 p.2))
    (h₂ : PT (fun p : α × ℕ × ℕ × ℕ => f₂ p.1 p.2.1 p.2.2.1 p.2.2.2))
    (h₃ : PT (fun p : α × ℕ × ℕ × ℕ => f₃ p.1 p.2.1 p.2.2.1 p.2.2.2)) (hg : PT g) :
    PT (fun a => (g a).elim (f₁ a) (f₂ a) (f₃ a)) := by
  have h : PT (fun a => Sum.elim (f₁ a) (Sum.elim (fun q => f₂ a q.1 q.2.1 q.2.2)
      (fun q => f₃ a q.1 q.2.1 q.2.2)) (g a).toSum) :=
    PT.sumElim h₁ (PT.sumElim (h₂.comp (PT.pair (PT.fst (PT.fst PT.id)) (PT.snd PT.id)))
      (h₃.comp (PT.pair (PT.fst (PT.fst PT.id)) (PT.snd PT.id))) PT.snd') (PT.gateToSum hg)
  exact h.of_eq fun a => (Gate.elim_eq _ _ _ (g a)).symm

@[fun_prop] protected theorem PT.compToProd {c : α → Comp} (hc : PT c) :
    PT (fun a => (c a).toProd) :=
  (PT.ofInj_to Comp.toProd Comp.ofProd (fun _ => rfl)).comp hc

@[fun_prop] protected theorem PT.compGates {c : α → Comp} (hc : PT c) :
    PT (fun a => (c a).gates) :=
  (PT.fst (PT.compToProd hc)).of_eq fun _ => rfl

@[fun_prop] protected theorem PT.compRes {c : α → Comp} (hc : PT c) :
    PT (fun a => (c a).res) :=
  (PT.fst (PT.snd (PT.compToProd hc))).of_eq fun _ => rfl

@[fun_prop] protected theorem PT.compCnt {c : α → Comp} (hc : PT c) :
    PT (fun a => (c a).cnt) :=
  (PT.snd (PT.snd (PT.compToProd hc))).of_eq fun _ => rfl

@[fun_prop] protected theorem PT.compMk {g : α → List CGate} {r : α → CVar} {n : α → ℕ}
    (hg : PT g) (hr : PT r) (hn : PT n) : PT (fun a => (⟨g a, r a, n a⟩ : Comp)) :=
  PT.ofInj_mk Comp.toProd Comp.ofProd (fun _ => rfl) (PT.pair hg (PT.pair hr hn))

@[fun_prop] protected theorem PT.shiftVar {k : α → ℕ} {v : α → CVar} (hk : PT k) (hv : PT v) :
    PT (fun a => shiftVar (k a) (v a)) := by
  have h : PT (fun a => Sum.elim (fun i => (Sum.inl i : CVar)) (fun j => Sum.inr (j + k a)) (v a)) :=
    by fun_prop
  exact h.of_eq fun a => by cases v a <;> rfl

@[fun_prop] protected theorem PT.place {n : α → ℕ} {v : α → CVar} (hn : PT n) (hv : PT v) :
    PT (fun a => place (n a) (v a)) := by
  have h : PT (fun a => Sum.elim (fun i => i) (fun j => n a + j) (v a)) := by fun_prop
  exact h.of_eq fun a => by cases v a <;> rfl

@[fun_prop] protected theorem PT.cgateShift {k : α → ℕ} {g : α → CGate} (hk : PT k) (hg : PT g) :
    PT (fun a => (g a).shift (k a)) := by
  have h : PT (fun a => (g a).elim (fun x => CGate.one (shiftVar (k a) x))
      (fun x y z => CGate.add (shiftVar (k a) x) (shiftVar (k a) y) (shiftVar (k a) z))
      (fun x y z => CGate.mul (shiftVar (k a) x) (shiftVar (k a) y) (shiftVar (k a) z))) :=
    PT.cgateElim (f₁ := fun a x => CGate.one (shiftVar (k a) x))
      (f₂ := fun a x y z => CGate.add (shiftVar (k a) x) (shiftVar (k a) y) (shiftVar (k a) z))
      (f₃ := fun a x y z => CGate.mul (shiftVar (k a) x) (shiftVar (k a) y) (shiftVar (k a) z))
      (by fun_prop) (by fun_prop) (by fun_prop) hg
  exact h.of_eq fun a => by cases g a <;> rfl

@[fun_prop] protected theorem PT.cgateToGate {n : α → ℕ} {g : α → CGate} (hn : PT n)
    (hg : PT g) : PT (fun a => (g a).toGate (n a)) := by
  have h : PT (fun a => (g a).elim (fun x => Gate.one (place (n a) x))
      (fun x y z => Gate.add (place (n a) x) (place (n a) y) (place (n a) z))
      (fun x y z => Gate.mul (place (n a) x) (place (n a) y) (place (n a) z))) :=
    PT.cgateElim (f₁ := fun a x => Gate.one (place (n a) x))
      (f₂ := fun a x y z => Gate.add (place (n a) x) (place (n a) y) (place (n a) z))
      (f₃ := fun a x y z => Gate.mul (place (n a) x) (place (n a) y) (place (n a) z))
      (by fun_prop) (by fun_prop) (by fun_prop) hg
  exact h.of_eq fun a => by cases g a <;> rfl

/-- The binary operations on compiled pieces, in uncurried form. -/
theorem PT.compOps :
    PT (fun p : Comp × Comp => p.1.addC p.2) ∧ PT (fun p : Comp × Comp => p.1.subC p.2) ∧
    PT (fun p : Comp × Comp => p.1.mulC p.2) ∧ PT (fun p : Comp × Comp => p.1.leC p.2) ∧
    PT (fun p : Comp × Comp => p.1.ltC p.2) ∧ PT (fun p : Comp × Comp => p.1.andC p.2) ∧
    PT (fun p : Comp × Comp => p.1.orC p.2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [Comp.addC, Comp.subC, Comp.mulC, Comp.leC, Comp.ltC, Comp.andC, Comp.orC,
        Comp.ext, Comp.pair]
      fun_prop

@[fun_prop] protected theorem PT.compAddC {c d : α → Comp} (hc : PT c) (hd : PT d) :
    PT (fun a => (c a).addC (d a)) := PT.compOps.1.comp (PT.pair hc hd)

@[fun_prop] protected theorem PT.compSubC {c d : α → Comp} (hc : PT c) (hd : PT d) :
    PT (fun a => (c a).subC (d a)) := PT.compOps.2.1.comp (PT.pair hc hd)

@[fun_prop] protected theorem PT.compMulC {c d : α → Comp} (hc : PT c) (hd : PT d) :
    PT (fun a => (c a).mulC (d a)) := PT.compOps.2.2.1.comp (PT.pair hc hd)

@[fun_prop] protected theorem PT.compLeC {c d : α → Comp} (hc : PT c) (hd : PT d) :
    PT (fun a => (c a).leC (d a)) := PT.compOps.2.2.2.1.comp (PT.pair hc hd)

@[fun_prop] protected theorem PT.compLtC {c d : α → Comp} (hc : PT c) (hd : PT d) :
    PT (fun a => (c a).ltC (d a)) := PT.compOps.2.2.2.2.1.comp (PT.pair hc hd)

@[fun_prop] protected theorem PT.compAndC {c d : α → Comp} (hc : PT c) (hd : PT d) :
    PT (fun a => (c a).andC (d a)) := PT.compOps.2.2.2.2.2.1.comp (PT.pair hc hd)

@[fun_prop] protected theorem PT.compOrC {c d : α → Comp} (hc : PT c) (hd : PT d) :
    PT (fun a => (c a).orC (d a)) := PT.compOps.2.2.2.2.2.2.comp (PT.pair hc hd)

end PTLemmas

/-! ### Sizes -/

namespace Circuit

theorem size_cvar_le {v : CVar} {n c : ℕ} (h : FLt c v ∧ OLt n v) : size v ≤ n + c + 1 := by
  rcases v with i | j
  · have := h.2
    simp only [OLt] at this
    simp only [size_inl, size_nat]
    omega
  · have := h.1
    simp only [FLt] at this
    simp only [size_inr, size_nat]
    omega

theorem size_cgate_le {g : CGate} {n c : ℕ} (h : g.All (fun v => FLt c v ∧ OLt n v)) :
    size g ≤ 3 * (n + c + 1) + 2 := by
  rw [size_cgate]
  rcases g with x | ⟨x, y, z⟩ | ⟨x, y, z⟩
  · have := size_cvar_le (n := n) (c := c) h
    simp only [CGate.toSum, size_inl]
    omega
  · obtain ⟨hx, hy, hz⟩ := h
    have := size_cvar_le hx
    have := size_cvar_le hy
    have := size_cvar_le hz
    simp only [CGate.toSum, size_inl, size_inr, size_prod]
    omega
  · obtain ⟨hx, hy, hz⟩ := h
    have := size_cvar_le hx
    have := size_cvar_le hy
    have := size_cvar_le hz
    simp only [CGate.toSum, size_inr, size_prod]
    omega

/-- The size of a well-formed compiled piece. -/
theorem size_comp_le (x : Comp) (n : ℕ) (hw : x.WF) (ho : x.OrigLt n) :
    size x ≤ (x.gates.length + 1) * (3 * (n + x.cnt + 1) + 3) + (n + x.cnt + 1) + (x.cnt + 1) := by
  have hg : size x.gates ≤ x.gates.length + 1 + x.gates.length * (3 * (n + x.cnt + 1) + 2) := by
    rw [size_list]
    have := sum_map_le_mul (l := x.gates) (g := size) (K := 3 * (n + x.cnt + 1) + 2)
      fun g hg => size_cgate_le ((hw.1 g hg).and (ho.1 g hg))
    omega
  have hr := size_cvar_le ⟨hw.2, ho.2⟩
  rw [size_comp, size_nat]
  have : (x.gates.length + 1) * (3 * (n + x.cnt + 1) + 3) =
      x.gates.length * (3 * (n + x.cnt + 1) + 2) + x.gates.length + (3 * (n + x.cnt + 1) + 3) := by
    ring
  omega

end Circuit

/-! ### The compilation as a catamorphism -/

namespace ETR

open Circuit

/-- The compiled constant `0`. -/
def zeroComp : Comp := ⟨[.add (.inr 0) (.inr 0) (.inr 0)], .inr 0, 1⟩

/-- The compiled constant `1`. -/
def oneComp : Comp := ⟨[.one (.inr 0)], .inr 0, 1⟩

/-- The compiled variable `x i`. -/
def varComp (i : ℕ) : Comp := ⟨[], .inl i, 0⟩

theorem Term.comp_eq_cata (t : Term) :
    t.cata varComp zeroComp oneComp Comp.addC Comp.subC Comp.mulC = t.comp := by
  induction t with
  | var i => rfl
  | zero => rfl
  | one => rfl
  | add s t ihs iht => simp only [Term.cata, Term.comp, ihs, iht]
  | sub s t ihs iht => simp only [Term.cata, Term.comp, ihs, iht]
  | mul s t ihs iht => simp only [Term.cata, Term.comp, ihs, iht]

/-- The compiled positive and negative normal forms of a formula, by one catamorphism. -/
def Formula.compPair (φ : Formula) : Comp × Comp :=
  φ.cata varComp zeroComp oneComp Comp.addC Comp.subC Comp.mulC
    (fun s t => (s.subC t, (s.ltC t).orC (t.ltC s))) (fun s t => (s.ltC t, t.leC s))
    (fun s t => (s.leC t, t.ltC s)) Prod.swap (fun p q => (p.1.andC q.1, p.2.orC q.2))
    (fun p q => (p.1.orC q.1, p.2.andC q.2))

theorem Formula.compPair_eq (φ : Formula) : φ.compPair = (φ.nnf.1.comp, φ.nnf.2.comp) := by
  induction φ with
  | eq s t => simp only [Formula.compPair, Formula.cata, Term.comp_eq_cata, Formula.nnf, NNF.comp]
  | lt s t => simp only [Formula.compPair, Formula.cata, Term.comp_eq_cata, Formula.nnf, NNF.comp]
  | le s t => simp only [Formula.compPair, Formula.cata, Term.comp_eq_cata, Formula.nnf, NNF.comp]
  | not φ ih =>
    simp only [Formula.compPair] at ih ⊢
    simp only [Formula.cata, ih, Formula.nnf, Prod.swap]
  | and φ ψ ih₁ ih₂ =>
    simp only [Formula.compPair] at ih₁ ih₂ ⊢
    simp only [Formula.cata, ih₁, ih₂, Formula.nnf, NNF.comp]
  | or φ ψ ih₁ ih₂ =>
    simp only [Formula.compPair] at ih₁ ih₂ ⊢
    simp only [Formula.cata, ih₁, ih₂, Formula.nnf, NNF.comp]

theorem Formula.compiled_eq (φ : Formula) : φ.compiled = φ.compPair.1 := by
  rw [Formula.compPair_eq]
  rfl

/-! ### Exact sizes of terms and formulas -/

theorem size_termVar (i : ℕ) : size (Term.var i) = i + 14 := by
  rw [size_term]
  simp only [Term.toks, size_cons, size_nil, size_nat]

theorem size_termZero : size Term.zero = 9 := by rw [size_term]; simp [Term.toks]

theorem size_termOne : size Term.one = 10 := by rw [size_term]; simp [Term.toks]

theorem size_termNode (f : Term → Term → Term) (k : ℕ)
    (hf : ∀ x y, (f x y).toks = k :: (x.toks ++ y.toks)) (s t : Term) :
    size (f s t) = size s + size t + k + 1 := by
  have := size_append s.toks t.toks
  rw [size_term, hf, size_term s, size_term t, size_cons, size_nat]
  omega

theorem size_formulaAtom (f : Term → Term → Formula) (k : ℕ)
    (hf : ∀ x y, (f x y).toks = k :: (x.toks ++ y.toks)) (s t : Term) :
    size (f s t) = size s + size t + k + 1 := by
  have := size_append s.toks t.toks
  rw [size_formula, hf, size_term s, size_term t, size_cons, size_nat]
  omega

theorem size_formulaNode (f : Formula → Formula → Formula) (k : ℕ)
    (hf : ∀ x y, (f x y).toks = k :: (x.toks ++ y.toks)) (φ ψ : Formula) :
    size (f φ ψ) = size φ + size ψ + k + 1 := by
  have := size_append φ.toks ψ.toks
  rw [size_formula, hf, size_formula φ, size_formula ψ, size_cons, size_nat]
  omega

theorem size_formulaNot (φ : Formula) : size (Formula.not φ) = size φ + 5 := by
  rw [size_formula, size_formula φ]
  simp only [Formula.toks, size_cons, size_nat]
  omega

theorem one_le_size_term (t : Term) : 1 ≤ size t := by
  rw [size_term]; exact size_pos_list _

/-! ### Bounds -/

theorem Term.varBound_le_size (t : Term) : t.varBound ≤ size t := by
  induction t with
  | var i => rw [size_termVar]; simp only [Term.varBound]; omega
  | zero => simp [Term.varBound]
  | one => simp [Term.varBound]
  | add s t ihs iht =>
    rw [size_termNode Term.add 8 (fun _ _ => rfl)]; simp only [Term.varBound]; omega
  | sub s t ihs iht =>
    rw [size_termNode Term.sub 9 (fun _ _ => rfl)]; simp only [Term.varBound]; omega
  | mul s t ihs iht =>
    rw [size_termNode Term.mul 10 (fun _ _ => rfl)]; simp only [Term.varBound]; omega

theorem Formula.varBound_le_size (φ : Formula) : φ.varBound ≤ size φ := by
  induction φ with
  | eq s t =>
    have := s.varBound_le_size; have := t.varBound_le_size
    rw [size_formulaAtom Formula.eq 0 (fun _ _ => rfl)]; simp only [Formula.varBound]; omega
  | lt s t =>
    have := s.varBound_le_size; have := t.varBound_le_size
    rw [size_formulaAtom Formula.lt 1 (fun _ _ => rfl)]; simp only [Formula.varBound]; omega
  | le s t =>
    have := s.varBound_le_size; have := t.varBound_le_size
    rw [size_formulaAtom Formula.le 2 (fun _ _ => rfl)]; simp only [Formula.varBound]; omega
  | not φ ih => rw [size_formulaNot]; simp only [Formula.varBound]; omega
  | and φ ψ ih₁ ih₂ =>
    rw [size_formulaNode Formula.and 4 (fun _ _ => rfl)]; simp only [Formula.varBound]; omega
  | or φ ψ ih₁ ih₂ =>
    rw [size_formulaNode Formula.or 5 (fun _ _ => rfl)]; simp only [Formula.varBound]; omega

section Counts

variable (c d : Comp)

@[simp] theorem addC_len : (c.addC d).gates.length = c.gates.length + d.gates.length + 1 := by
  simp [Comp.addC, Comp.ext, Comp.pair]; omega
@[simp] theorem subC_len : (c.subC d).gates.length = c.gates.length + d.gates.length + 1 := by
  simp [Comp.subC, Comp.ext, Comp.pair]; omega
@[simp] theorem mulC_len : (c.mulC d).gates.length = c.gates.length + d.gates.length + 1 := by
  simp [Comp.mulC, Comp.ext, Comp.pair]; omega
@[simp] theorem orC_len : (c.orC d).gates.length = c.gates.length + d.gates.length + 1 := by
  simp [Comp.orC, Comp.ext, Comp.pair]; omega
@[simp] theorem leC_len : (c.leC d).gates.length = c.gates.length + d.gates.length + 3 := by
  simp [Comp.leC, Comp.ext, Comp.pair]; omega
@[simp] theorem andC_len : (c.andC d).gates.length = c.gates.length + d.gates.length + 3 := by
  simp [Comp.andC, Comp.ext, Comp.pair]; omega
@[simp] theorem ltC_len : (c.ltC d).gates.length = c.gates.length + d.gates.length + 5 := by
  simp [Comp.ltC, Comp.ext, Comp.pair]; omega
@[simp] theorem addC_cnt : (c.addC d).cnt = c.cnt + d.cnt + 1 := rfl
@[simp] theorem subC_cnt : (c.subC d).cnt = c.cnt + d.cnt + 1 := rfl
@[simp] theorem mulC_cnt : (c.mulC d).cnt = c.cnt + d.cnt + 1 := rfl
@[simp] theorem orC_cnt : (c.orC d).cnt = c.cnt + d.cnt + 1 := rfl
@[simp] theorem leC_cnt : (c.leC d).cnt = c.cnt + d.cnt + 4 := rfl
@[simp] theorem andC_cnt : (c.andC d).cnt = c.cnt + d.cnt + 3 := rfl
@[simp] theorem ltC_cnt : (c.ltC d).cnt = c.cnt + d.cnt + 6 := rfl

end Counts

theorem Term.comp_len_le (t : Term) : t.comp.gates.length ≤ size t ∧ t.comp.cnt ≤ size t := by
  induction t with
  | var i => rw [size_termVar]; simp [Term.comp]
  | zero => rw [size_termZero]; simp [Term.comp]
  | one => rw [size_termOne]; simp [Term.comp]
  | add s t ihs iht =>
    rw [size_termNode Term.add 8 (fun _ _ => rfl)]; simp only [Term.comp, addC_len, addC_cnt]
    omega
  | sub s t ihs iht =>
    rw [size_termNode Term.sub 9 (fun _ _ => rfl)]; simp only [Term.comp, subC_len, subC_cnt]
    omega
  | mul s t ihs iht =>
    rw [size_termNode Term.mul 10 (fun _ _ => rfl)]; simp only [Term.comp, mulC_len, mulC_cnt]
    omega

theorem Formula.compPair_len_le (φ : Formula) :
    φ.nnf.1.comp.gates.length ≤ 11 * size φ ∧ φ.nnf.1.comp.cnt ≤ 11 * size φ ∧
      φ.nnf.2.comp.gates.length ≤ 11 * size φ ∧ φ.nnf.2.comp.cnt ≤ 11 * size φ := by
  induction φ with
  | eq s t =>
    have := s.comp_len_le; have := t.comp_len_le; have := one_le_size_term s
    rw [size_formulaAtom Formula.eq 0 (fun _ _ => rfl)]
    simp only [Formula.nnf, NNF.comp, subC_len, subC_cnt, orC_len, orC_cnt, ltC_len, ltC_cnt]
    omega
  | lt s t =>
    have := s.comp_len_le; have := t.comp_len_le
    rw [size_formulaAtom Formula.lt 1 (fun _ _ => rfl)]
    simp only [Formula.nnf, NNF.comp, ltC_len, ltC_cnt, leC_len, leC_cnt]
    omega
  | le s t =>
    have := s.comp_len_le; have := t.comp_len_le
    rw [size_formulaAtom Formula.le 2 (fun _ _ => rfl)]
    simp only [Formula.nnf, NNF.comp, ltC_len, ltC_cnt, leC_len, leC_cnt]
    omega
  | not φ ih =>
    rw [size_formulaNot]
    simp only [Formula.nnf, Prod.fst_swap, Prod.snd_swap]
    omega
  | and φ ψ ih₁ ih₂ =>
    rw [size_formulaNode Formula.and 4 (fun _ _ => rfl)]
    simp only [Formula.nnf, NNF.comp, andC_len, andC_cnt, orC_len, orC_cnt]
    omega
  | or φ ψ ih₁ ih₂ =>
    rw [size_formulaNode Formula.or 5 (fun _ _ => rfl)]
    simp only [Formula.nnf, NNF.comp, andC_len, andC_cnt, orC_len, orC_cnt]
    omega

/-- The common size bound of the compiled pieces. -/
def compBound (N : ℕ) : ℕ := (11 * N + 1) * (3 * (22 * N + 1) + 3) + 2 * (22 * N + 1)

theorem compBound_poly : PolynomialBound compBound := by
  unfold compBound
  exact (((PolynomialBound.constant 11).mul PolynomialBound.identity).add
    (PolynomialBound.constant 1)).mul ((PolynomialBound.constant 3).mul
      (((PolynomialBound.constant 22).mul PolynomialBound.identity).add
        (PolynomialBound.constant 1)) |>.add (PolynomialBound.constant 3)) |>.add
    ((PolynomialBound.constant 2).mul (((PolynomialBound.constant 22).mul
      PolynomialBound.identity).add (PolynomialBound.constant 1)))

theorem size_comp_le_bound {x : Comp} {n N : ℕ} (hw : x.WF) (ho : x.OrigLt n)
    (hl : x.gates.length ≤ 11 * N) (hc : x.cnt ≤ 11 * N) (hn : n ≤ 11 * N) :
    size x ≤ compBound N := by
  have h := size_comp_le x n hw ho
  have h2 : (x.gates.length + 1) * (3 * (n + x.cnt + 1) + 3) ≤
      (11 * N + 1) * (3 * (22 * N + 1) + 3) := Nat.mul_le_mul (by omega) (by omega)
  unfold compBound
  omega

end ETR

/-! ### Polynomial time -/

open ETR

theorem PT.compPair : PT Formula.compPair := by
  have hops := PT.compOps
  refine PT.formulaCata (φ := fun φ : Formula => φ)
    (fv := fun _ => varComp) (fz := fun _ => zeroComp) (fo := fun _ => oneComp)
    (fadd := fun _ => Comp.addC) (fsub := fun _ => Comp.subC) (fmul := fun _ => Comp.mulC)
    (feq := fun _ s t => (s.subC t, (s.ltC t).orC (t.ltC s)))
    (flt := fun _ s t => (s.ltC t, t.leC s)) (fle := fun _ s t => (s.leC t, t.ltC s))
    (fnot := fun _ => Prod.swap) (fAnd := fun _ p q => (p.1.andC q.1, p.2.orC q.2))
    (fOr := fun _ p q => (p.1.orC q.1, p.2.andC q.2))
    (by unfold varComp; fun_prop) (PT.const _) (PT.const _) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) PT.id (fun N => 2 * compBound N)
    ((PolynomialBound.constant 2).mul compBound_poly) ?_ ?_
  · intro φ u hu
    rw [Term.comp_eq_cata]
    have hs := size_le_of_mem_formula_subterms hu
    have hl := u.comp_len_le
    have hv := u.varBound_le_size
    have := size_comp_le_bound (N := size φ) u.comp_wf (u.comp_orig u.varsLt_varBound)
      (by omega) (by omega) (by omega)
    omega
  · intro φ ψ hψ
    have h := Formula.compPair_eq ψ
    simp only [Formula.compPair] at h
    rw [h]
    simp only [size_prod]
    have hs := size_le_of_mem_subformulas hψ
    have hl := ψ.compPair_len_le
    have hv := ψ.varBound_le_size
    have ho := ψ.nnf_varsLt ψ.varsLt_varBound
    have h1 := size_comp_le_bound (N := size φ) ψ.nnf.1.comp_wf (ψ.nnf.1.comp_orig ho.1)
      (by omega) (by omega) (by omega)
    have h2 := size_comp_le_bound (N := size φ) ψ.nnf.2.comp_wf (ψ.nnf.2.comp_orig ho.2)
      (by omega) (by omega) (by omega)
    omega

@[fun_prop] protected theorem PT.compiled {α : Type} [Code α] {φ : α → Formula} (hφ : PT φ) :
    PT (fun a => (φ a).compiled) :=
  ((PT.fst PT.compPair).comp hφ).of_eq fun a => (Formula.compiled_eq (φ a)).symm

theorem Formula.varBound_eq_cata (φ : Formula) :
    φ.varBound = φ.cata (fun i => i + 1) 0 0 max max max max max max id max max := by
  have ht : ∀ t : Term, t.varBound = t.cata (fun i => i + 1) 0 0 max max max := by
    intro t
    induction t with
    | var i => rfl
    | zero => rfl
    | one => rfl
    | add s t ihs iht => simp only [Term.varBound, Term.cata, ihs, iht]
    | sub s t ihs iht => simp only [Term.varBound, Term.cata, ihs, iht]
    | mul s t ihs iht => simp only [Term.varBound, Term.cata, ihs, iht]
  induction φ with
  | eq s t => simp only [Formula.varBound, Formula.cata, ht]
  | lt s t => simp only [Formula.varBound, Formula.cata, ht]
  | le s t => simp only [Formula.varBound, Formula.cata, ht]
  | not φ ih => simp only [Formula.varBound, Formula.cata, ih, id]
  | and φ ψ ih₁ ih₂ => simp only [Formula.varBound, Formula.cata, ih₁, ih₂]
  | or φ ψ ih₁ ih₂ => simp only [Formula.varBound, Formula.cata, ih₁, ih₂]

theorem PT.formulaVarBound' : PT Formula.varBound := by
  have ht : ∀ t : Term, t.cata (fun i => i + 1) 0 0 max max max = t.varBound := by
    intro t
    induction t with
    | var i => rfl
    | zero => rfl
    | one => rfl
    | add s t ihs iht => simp only [Term.varBound, Term.cata, ihs, iht]
    | sub s t ihs iht => simp only [Term.varBound, Term.cata, ihs, iht]
    | mul s t ihs iht => simp only [Term.varBound, Term.cata, ihs, iht]
  refine (PT.formulaCata (φ := fun φ : Formula => φ) (fv := fun _ i => i + 1)
    (fz := fun _ => 0) (fo := fun _ => 0) (fadd := fun _ => max) (fsub := fun _ => max)
    (fmul := fun _ => max) (feq := fun _ => max) (flt := fun _ => max) (fle := fun _ => max)
    (fnot := fun _ => id) (fAnd := fun _ => max) (fOr := fun _ => max)
    (by fun_prop) (PT.const _) (PT.const _) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) (by simp only [id]; fun_prop) (by fun_prop)
    (by fun_prop) PT.id (fun N => N + 1)
    (PolynomialBound.identity.add (PolynomialBound.constant 1)) ?_ ?_).of_eq
    fun φ => (Formula.varBound_eq_cata φ).symm
  · intro φ u hu
    rw [ht, size_nat]
    have := size_le_of_mem_formula_subterms hu
    have := u.varBound_le_size
    omega
  · intro φ ψ hψ
    rw [← Formula.varBound_eq_cata, size_nat]
    have := size_le_of_mem_subformulas hψ
    have := ψ.varBound_le_size
    omega

@[fun_prop] protected theorem PT.formulaVarBound {α : Type} [Code α] {φ : α → Formula}
    (hφ : PT φ) : PT (fun a => (φ a).varBound) :=
  PT.formulaVarBound'.comp hφ

@[fun_prop] protected theorem PT.toCircuit {α : Type} [Code α] {φ : α → Formula} (hφ : PT φ) :
    PT (fun a => (φ a).toCircuit) := by
  unfold Formula.toCircuit
  fun_prop

@[fun_prop] protected theorem PT.circuitVars {α : Type} [Code α] {φ : α → Formula} (hφ : PT φ) :
    PT (fun a => (φ a).circuitVars) := by
  unfold Formula.circuitVars
  fun_prop

end ArtGallery

end
