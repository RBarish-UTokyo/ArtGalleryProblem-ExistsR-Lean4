module

public import PT.Raw
public import PT.ListBasic

/-!
# Examples and regression tests for the `PT` framework

## Proving `PT (fun a => …)` goals

* `fun_prop` proves goals built from the tagged operations: pairs and projections,
  `if … then … else` (on `Bool`s or decidable propositions built from `=`, `≤`, `<`, `∣`, `∧`,
  `∨`, `¬` on `Nat`/`Bool`), `bif`, Boolean connectives, unary arithmetic
  (`+ - * / % min max succ pred`, `^ k` for a numeral `k`), `Option` (`some`, `getD`,
  `isSome`, `elim`, `map`, `bind`), sums, lists (`::`, `++`, `head?`, `headD`, `tail`,
  `isEmpty`, `length`, `reverse`, `map`), `SAT.Literal` fields, `pairWords`/`unpair`, and
  hypotheses `PT f` / `PT (fun p : β × γ => f p.1 p.2)` about free functions.
* `fun_prop` does not see through a `match` on an option/list/sum, or through recursion.
  For a `match`, use `PT.of_optionCases` / `PT.of_listCases` / `PT.of_natCases` /
  `PT.of_sumCases` (or `PT.of_eq` from the `Option.elim` form).  For recursion use
  `PT.iterate`, `PT.of_natRec`, `PT.foldl`, `PT.foldr` and supply the size bound.
* For your own function `myFun : β → γ → δ`, prove
  `PT (fun p : β × γ => myFun p.1 p.2)` once and derive the compositional form with
  `PT.comp₂`, tagging it `@[fun_prop]`.
* Declare lemmas as `protected theorem PT.foo`: without `protected`, names such as `id`,
  `some`, `min`, `map` would resolve to the `PT` lemmas inside later `theorem PT.bar`
  declarations.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.PT.Examples

open Complexity Complexity.PT

/-! ### `fun_prop` -/

example : PT (fun p : Nat × Nat => (p.1 + p.2 * p.1, p.2)) := by fun_prop
example : PT (fun p : (Nat × Bool) × Nat => if p.1.2 then p.2 + 1 else p.1.1) := by fun_prop
example : PT (fun p : Nat × Nat => if p.1 ≤ p.2 then p.2 - p.1 else p.1 % (p.2 + 1)) := by
  fun_prop
example : PT (fun p : Nat × Nat => if p.1 ≥ p.2 ∧ p.1 ≠ 3 then p.2 / 2 else p.1 ^ 3) := by
  fun_prop
example : PT (fun p : Nat × Nat =>
    (p.1 == p.2, p.1 != p.2, decide (p.1 > p.2), max p.1 p.2, min p.1 3, p.1.succ, p.2.pred)) := by
  fun_prop
example : PT (fun p : Nat × Nat => (p.1 < p.2 : Bool) || p.1 ∣ p.2) := by fun_prop
example : PT (fun p : (Nat × Bool) × Bool => bif p.1.2 && !p.2 then p.1.1 else 0) := by fun_prop
example : PT (fun p : (Nat × Bool) × Bool => (p.1.2 == p.2, p.2 != p.1.2, decide (p.2 = p.1.2))) := by
  fun_prop
example : PT (fun p : Nat × Nat => let q := p.1 + p.2; q * q) := by fun_prop
example : PT (fun p : Nat × Nat => match p with | (a, b) => a + b) := by fun_prop
example : PT (fun p : Nat × List Nat => p.2.map (fun n => n * p.1 + 1)) := by fun_prop
example : PT (fun p : Nat × List Nat =>
    (p.1 :: p.2.reverse ++ p.2.tail, p.2.length, p.2.head?, p.2.isEmpty, p.2.headD 0)) := by
  fun_prop
example : PT (fun p : Option Nat × Nat => p.1.getD p.2 + (p.1.map (· + p.2)).getD 0) := by
  fun_prop
example : PT (fun p : Option Nat × Nat => p.1.elim p.2 (fun b => b + p.2)) := by fun_prop
example : PT (fun p : Option Nat × Nat =>
    p.1.bind (fun b => if b = p.2 then none else some (b, p.2))) := by fun_prop
example : PT (fun s : Nat ⊕ Bool => Sum.elim (fun n => n + 1) (fun b => if b then 1 else 0) s) := by
  fun_prop
example : PT (fun f : SAT.CNF =>
    f.map (fun c => c.map (fun l => (⟨l.var + 1, !l.positive⟩ : SAT.Literal)))) := by fun_prop
example : PT (fun w : Word × Word => pairWords w.2 (true :: w.1)) := by fun_prop
example (f : Nat → Bool) (hf : PT f) : PT (fun p : Nat × Nat => f p.1 || f p.2) := by fun_prop
example (f : Nat → Nat → Nat) (hf : PT (fun p : Nat × Nat => f p.1 p.2)) :
    PT (fun p : Nat × Nat => f (p.2 + 1) (f p.1 p.1)) := by fun_prop
example (f : Nat → Nat → Nat) (hf : PT (fun p : Nat × Nat => f p.1 p.2)) :
    PT (fun p : List Nat × Nat => p.1.map (fun n => f n p.2)) := by fun_prop

/-! ### `match` -/

example : PT (fun p : Option Nat × Nat => match p.1 with | none => p.2 | some b => b + p.2) := by
  refine PT.of_optionCases (o := fun p => p.1) (d := fun p => p.2) (f := fun p b => b + p.2)
    (by fun_prop) (by fun_prop) (by fun_prop) ?_ ?_
  · intro p h; simp [h]
  · intro p b h; simp [h]

example : PT (fun p : Option Nat × Nat => match p.1 with | none => p.2 | some b => b + p.2) := by
  refine PT.of_eq (f := fun p => p.1.elim p.2 (fun b => b + p.2)) (by fun_prop) fun p => ?_
  cases p.1 <;> rfl

example : PT (fun p : List Nat × Nat => match p.1 with | [] => p.2 | a :: t => a + t.length) := by
  refine PT.of_listCases (l := fun p => p.1) (d := fun p => p.2) (f := fun _ a t => a + t.length)
    (by fun_prop) (by fun_prop) (by fun_prop) ?_ ?_
  · intro p h; simp [h]
  · intro p a t h; simp [h]

example : PT (fun p : Nat × Nat => match p.1 with | 0 => p.2 | k + 1 => k * p.2) := by
  apply PT.natCases <;> fun_prop

/-! ### Bounded recursion -/

/-- The sum of a list of numbers, by a bounded fold. -/
example : PT (fun l : List Nat => l.foldl (· + ·) 0) := by
  refine PT.foldl (f := fun _ s b => s + b) (init := fun _ => 0) (l := fun l => l)
    (by fun_prop) (by fun_prop) (by fun_prop) (fun n => n) PolynomialBound.identity ?_
  intro l pre hpre
  have h1 := size_le_of_prefix hpre
  have h2 : ∀ (t : List Nat) (s : Nat), size (t.foldl (· + ·) s) + 2 * t.length = s + size t := by
    intro t
    induction t with
    | nil => intro s; simp
    | cons a t ih => intro s; have := ih (s + a); simp only [List.foldl_cons, size_cons,
        List.length_cons, size_nat] at this ⊢; omega
  have := h2 pre 0
  omega

/-- Triangular numbers, by bounded primitive recursion. -/
def tri : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + tri n

theorem tri_le (n : Nat) : tri n ≤ n * n := by
  induction n with
  | zero => simp [tri]
  | succ n ih => simp only [tri, Nat.succ_mul, Nat.mul_succ]; omega

example : PT tri := by
  refine PT.of_natRec (g := fun _ i => tri i) (base := fun _ => 0)
    (step := fun _ i s => (i + 1) + s) (n := fun n => n) (by fun_prop) (by fun_prop)
    (by fun_prop) (fun _ => rfl) (fun _ _ => rfl) (fun N => N * N + 1)
    ((PolynomialBound.identity.mul PolynomialBound.identity).add (PolynomialBound.constant 1)) ?_
  intro n i hi
  have := tri_le i
  have := Nat.mul_le_mul hi hi
  simp only [size_nat, Nat.succ_mul, Nat.mul_succ]
  omega

/-! ### Raw words -/

/-- A `PT` function on formulas, as a polynomial-time function on codes. -/
example : ∃ F : Word → Word, PolyTime F ∧
    ∀ f : SAT.CNF, F (SAT.encode f) = SAT.encode (f.map List.reverse) := by
  have h : PT (fun f : SAT.CNF => f.map List.reverse) := by fun_prop
  exact h

example : PolyTime (fun x : Word => x.reverse ++ x) :=
  PT.polyTime_word (by fun_prop)

end Complexity.PT.Examples
