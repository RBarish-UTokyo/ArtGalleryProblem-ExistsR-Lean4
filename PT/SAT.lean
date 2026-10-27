module

public import PT.ListMore
public import Complexity.PCP.Defs

/-!
# Polynomial-time evaluation of CNF formulas

`SAT.Assignment = Nat → Bool` is not a coded type, so an assignment enters a `PT` statement as
a function `asg : α → SAT.Assignment` of the environment whose uncurried form
`fun q : α × Nat => asg q.1 q.2` is polynomial-time (`PT.evalLiteral`, `PT.evalClause`,
`PT.evalCNF`, `PT.satCount`).  The main instance is the assignment `SAT.assignmentOf y`
written by a word `y` (`PT.assignmentOf`), for which the uncurried statements are
`PT.evalLiteral_assignmentOf`, `PT.evalClause_assignmentOf`, `PT.evalCNF_assignmentOf` and
`PT.satCount_assignmentOf`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.PT

open Complexity.Reg Code

variable {α β : Type} [Code α] [Code β]

/-! ### Sizes and codes -/

/-- The size of a value (the length of its code), in unary. -/
@[fun_prop] protected theorem PT.size {f : α → β} (hf : PT f) : PT (fun a => size (f a)) :=
  PT.length (PT.enc hf)

/-- The length of the code of a value, in unary. -/
protected theorem PT.encLength {f : α → β} (hf : PT f) :
    PT (fun a => (Code.enc (f a) : Word).length) :=
  PT.length (PT.enc hf)

@[fun_prop] protected theorem PT.encodeLiteral {l : α → SAT.Literal} (hl : PT l) :
    PT (fun a => SAT.encodeLiteral (l a)) :=
  PT.enc hl

@[fun_prop] protected theorem PT.encodeClause {c : α → SAT.Clause} (hc : PT c) :
    PT (fun a => SAT.encodeClause (c a)) :=
  PT.enc hc

/-- `SAT.encode`, as a function into words. -/
@[fun_prop] protected theorem PT.encode {f : α → SAT.CNF} (hf : PT f) :
    PT (fun a => SAT.encode (f a)) :=
  PT.enc hf

/-- A `PT` function from raw words to formulas, as a polynomial-time function into codes. -/
protected theorem PT.polyTime_encode {V : Word → SAT.CNF} (hV : PT V) :
    PolyTime (fun w => SAT.encode (V w)) :=
  hV.polyTime

/-- The number of clauses of a formula. -/
protected theorem PT.cnfLength : PT (fun f : SAT.CNF => f.length) := PT.length PT.id

/-- The length of the code of a formula, in unary. -/
protected theorem PT.cnfEncLength : PT (fun f : SAT.CNF => (Code.enc f : Word).length) :=
  PT.encLength PT.id

/-- The 3-CNF test. -/
@[fun_prop] protected theorem PT.isThreeCNF {f : α → SAT.CNF}
    [inst : ∀ a, Decidable (SAT.IsThreeCNF (f a))] (hf : PT f) :
    PT (fun a => decide (SAT.IsThreeCNF (f a))) := by
  have h : PT (fun a => decide (∀ c ∈ f a, c.length ≤ 3)) := by fun_prop
  exact h.decide_congr fun _ => Iff.rfl

/-! ### Variable bounds -/

theorem clauseBound_lt_size (c : SAT.Clause) : SAT.clauseBound c < size c := by
  induction c with
  | nil => simp [SAT.clauseBound]
  | cons l c ih =>
    simp only [SAT.clauseBound, size_cons, size_literal]
    omega

theorem variableBound_lt_size (f : SAT.CNF) : SAT.variableBound f < size f := by
  induction f with
  | nil => simp [SAT.variableBound]
  | cons c f ih =>
    have := clauseBound_lt_size c
    simp only [SAT.variableBound, size_cons]
    omega

@[fun_prop] protected theorem PT.clauseBound {c : α → SAT.Clause} (hc : PT c) :
    PT (fun a => SAT.clauseBound (c a)) := by
  obtain ⟨d, k, hk⟩ := hc.size_le
  refine PT.of_listRec (g := fun _ t => SAT.clauseBound t) (base := fun _ => 0)
    (step := fun _ l _ r => max (l.var + 1) r) (PT.const 0)
    (PT.max (PT.succ (PT.literalVar (PT.fst PT.snd'))) (PT.snd (PT.snd PT.snd'))) hc
    (fun _ => rfl) (fun _ _ _ => rfl) (powerBound d k) (PolynomialBound.power d k) ?_
  intro a suf hsuf
  have h1 := clauseBound_lt_size suf
  have h2 := size_le_of_sublist hsuf.sublist
  have h3 := hk a
  rw [size_nat]
  omega

@[fun_prop] protected theorem PT.variableBound {f : α → SAT.CNF} (hf : PT f) :
    PT (fun a => SAT.variableBound (f a)) := by
  obtain ⟨d, k, hk⟩ := hf.size_le
  refine PT.of_listRec (g := fun _ t => SAT.variableBound t) (base := fun _ => 0)
    (step := fun _ c _ r => max (SAT.clauseBound c) r) (PT.const 0)
    (PT.max (PT.clauseBound (PT.fst PT.snd')) (PT.snd (PT.snd PT.snd'))) hf
    (fun _ => rfl) (fun _ _ _ => rfl) (powerBound d k) (PolynomialBound.power d k) ?_
  intro a suf hsuf
  have h1 := variableBound_lt_size suf
  have h2 := size_le_of_sublist hsuf.sublist
  have h3 := hk a
  rw [size_nat]
  omega

/-! ### Evaluation under an assignment computed from the environment -/

/-- The assignment written by a word, at a variable. -/
@[fun_prop] protected theorem PT.assignmentOf {y : α → Word} {i : α → Nat} (hy : PT y)
    (hi : PT i) : PT (fun a => SAT.assignmentOf (y a) (i a)) :=
  PT.listGetD hy hi (PT.const false)

@[fun_prop] protected theorem PT.evalLiteral {asg : α → SAT.Assignment} {l : α → SAT.Literal}
    (hasg : PT (fun q : α × Nat => asg q.1 q.2)) (hl : PT l) :
    PT (fun a => SAT.evalLiteral (asg a) (l a)) := by
  have h : PT (fun a => if (l a).positive then asg a (l a).var else !(asg a (l a).var)) :=
    PT.ite (PT.literalPositive hl) (hasg.comp (PT.pair PT.id (PT.literalVar hl)))
      (PT.not (hasg.comp (PT.pair PT.id (PT.literalVar hl))))
  exact h.of_eq fun _ => rfl

@[fun_prop] protected theorem PT.evalClause {asg : α → SAT.Assignment} {c : α → SAT.Clause}
    (hasg : PT (fun q : α × Nat => asg q.1 q.2)) (hc : PT c) :
    PT (fun a => SAT.evalClause (asg a) (c a)) :=
  (PT.any (p := fun a l => SAT.evalLiteral (asg a) l)
    (PT.evalLiteral (asg := fun q : α × SAT.Literal => asg q.1)
      (hasg.comp (PT.pair (PT.fst PT.fst') PT.snd')) PT.snd') hc).of_eq fun _ => rfl

@[fun_prop] protected theorem PT.evalCNF {asg : α → SAT.Assignment} {f : α → SAT.CNF}
    (hasg : PT (fun q : α × Nat => asg q.1 q.2)) (hf : PT f) :
    PT (fun a => SAT.evalCNF (asg a) (f a)) :=
  (PT.all (p := fun a c => SAT.evalClause (asg a) c)
    (PT.evalClause (asg := fun q : α × SAT.Clause => asg q.1)
      (hasg.comp (PT.pair (PT.fst PT.fst') PT.snd')) PT.snd') hf).of_eq fun _ => rfl

@[fun_prop] protected theorem PT.satCount {asg : α → SAT.Assignment} {f : α → SAT.CNF}
    (hasg : PT (fun q : α × Nat => asg q.1 q.2)) (hf : PT f) :
    PT (fun a => SAT.satCount (asg a) (f a)) :=
  (PT.countP (p := fun a c => SAT.evalClause (asg a) c)
    (PT.evalClause (asg := fun q : α × SAT.Clause => asg q.1)
      (hasg.comp (PT.pair (PT.fst PT.fst') PT.snd')) PT.snd') hf).of_eq fun _ => rfl

/-! ### Evaluation under the assignment written by a word -/

protected theorem PT.evalLiteral_assignmentOf :
    PT (fun p : Word × SAT.Literal => SAT.evalLiteral (SAT.assignmentOf p.1) p.2) :=
  PT.evalLiteral (PT.assignmentOf (PT.fst PT.fst') PT.snd') PT.snd'

protected theorem PT.evalClause_assignmentOf :
    PT (fun p : Word × SAT.Clause => SAT.evalClause (SAT.assignmentOf p.1) p.2) :=
  PT.evalClause (PT.assignmentOf (PT.fst PT.fst') PT.snd') PT.snd'

protected theorem PT.evalCNF_assignmentOf :
    PT (fun p : Word × SAT.CNF => SAT.evalCNF (SAT.assignmentOf p.1) p.2) :=
  PT.evalCNF (PT.assignmentOf (PT.fst PT.fst') PT.snd') PT.snd'

protected theorem PT.satCount_assignmentOf :
    PT (fun p : Word × SAT.CNF => SAT.satCount (SAT.assignmentOf p.1) p.2) :=
  PT.satCount (PT.assignmentOf (PT.fst PT.fst') PT.snd') PT.snd'

end Complexity.PT
