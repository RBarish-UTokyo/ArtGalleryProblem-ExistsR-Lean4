module

public import PT.Words
public import PT.SAT
public import PT.RawMore

/-!
# Examples and regression tests for the list, arithmetic and SAT libraries

(Continues `PT/Examples.lean`.)

## What `fun_prop` proves

In addition to the operations listed in `PT/Examples.lean`, `fun_prop` handles, with no side
conditions:

* lists: `filter`, `filterMap`, `flatMap`, `flatten`, `partition`, `any`, `all`, `and`, `or`,
  `countP`, `count`, `find?`, `findSome?`, `findIdx`, `idxOf`, `take`, `drop`, `splitAt`,
  `takeWhile`, `dropWhile`, `l[i]?`, `l[i]!`, `getD`, `head!`, `getLast?`, `getLastD`,
  `dropLast`, `set`, `eraseIdx`, `zip`, `zipWith`, `unzip`, `zipIdx`, `range`, `range'`,
  `replicate`, `sum`, `foldl max s`, `foldl min s`, `max?`, `min?` (on `List Nat`),
  `contains`, `elem`, `lookup`, `erase`, `insert`, `removeAll`, `eraseDups`;
* equality on *every* coded type: `decide (x = y)`, `decide (x ≠ y)`, `x == y`, `x != y`
  (`==` must come from a `LawfulBEq` instance, e.g. the derived or `DecidableEq` one; core
  has no `LawfulBEq` instance for sums, so use `decide (x = y)` there);
* `decide (x ∈ l)`, `decide (∀ x ∈ l, P x)`, `decide (∃ x ∈ l, P x)`, `decide (l ⊆ m)`;
* numbers: `Nat.log2`, `2 ^ Nat.log2 m`, `2 ^ (B * Nat.log2 m)` (`B` a constant), `Bool.toNat`;
* words: `natBits n`, `unary n`, `allWords (c * Nat.log2 m)`, `size x`, `SAT.encode f`;
* SAT: `SAT.evalLiteral`, `SAT.evalClause`, `SAT.evalCNF`, `SAT.satCount` under an assignment
  `asg` such that `fun q => asg q.1 q.2` is polynomial-time, in particular
  `SAT.assignmentOf y` and `fun i => decide (i ∈ l)`; `SAT.clauseBound`, `SAT.variableBound`,
  `decide (SAT.IsThreeCNF f)`.

## What needs a size bound

Numbers are in unary, so operations with exponentially large values need a hypothesis:
`PT.pow_of_le`, `PT.two_pow_of_le`, `PT.binValue_foldl`, `PT.binaryValue`, `PT.allWords`
take `bound : Nat → Nat`, `PolynomialBound bound` and a pointwise inequality in terms of
`size a`.  Useful facts for discharging it: `size_nat`, `size_prod`, `size_word`,
`size_cons`, `size_le_of_mem`, `size_le_of_sublist`, `length_lt_size`, `two_pow_log2_le`,
`two_pow_mul_log2_le`, and `PT.nat_le` / `PT.size_le` for the values of `PT` functions.
General recursion: `PT.of_listRec` (structural recursion on a list), `PT.of_natRec`,
`PT.foldl`, and the folds with simple growth conditions `PT.foldl_of_add_le`,
`PT.foldl_of_size_le`.

## Pitfalls

* `fun_prop` does not unfold definitions: unfold your own functions first (`unfold foo`, or
  `PT.of_eq`), or prove a compositional lemma about them and tag it `@[fun_prop]`.
* A `match` is not seen by `fun_prop`; use `PT.of_optionCases`, `PT.of_listCases`,
  `PT.of_natCases`, `PT.of_sumCases` (see below), or rewrite with `Option.elim` etc.
* Predicates must be Boolean-valued functions; write `fun x => decide (x < n)` or let Lean
  insert the coercion.  `l[i]` with a bound proof is not handled automatically (`PT.getElem`).
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.PT.Examples

open Complexity Complexity.PT

/-! ### Lists -/

example : PT (fun f : SAT.CNF =>
    f.flatMap (fun c => if c.length ≤ 3 then [c.take 2, c.drop 2] else [])) := by fun_prop
example : PT (fun p : Nat × List (List Nat) =>
    (List.range p.1).filter (fun i => p.2.any (fun t => decide (i ∈ t)))) := by fun_prop
example : PT (fun f : SAT.CNF => (f.zipIdx.map (fun q => (q.2, q.1.length)))) := by fun_prop
example : PT (fun p : Nat × List Nat =>
    (p.2.take p.1, p.2.drop 2, p.2[p.1]?, p.2.getD 3 p.1, p.2[0]!, p.2.getLast?, p.2.dropLast,
      p.2.splitAt 3, p.2.eraseIdx 2, p.2.set 2 5)) := by fun_prop
example : PT (fun p : List Nat × List Bool =>
    (p.1.flatMap (fun x => p.2.map (fun y => (x, y))), p.1.zip p.2,
      List.zipWith (fun x y => if y then x else 0) p.1 p.2, (p.1.zip p.2).unzip)) := by fun_prop
example : PT (fun p : List Nat × List Bool =>
    (p.1.takeWhile (· < 3), p.1.dropWhile (fun x => p.2.contains (x == 2)), p.1.findIdx (· == 2),
      List.replicate p.1.length p.2, p.1.sum, p.2.and, p.2.or, p.1.foldl max 0)) := by fun_prop
example : PT (fun p : List Nat × List Bool =>
    (p.1.partition (· < 3), p.1.filterMap (fun x => if x < 2 then some (x, p.2) else none),
      p.1.zipIdx 1, List.range' 2 p.1.length, List.range' 2 p.1.length 3)) := by fun_prop
example : PT (fun p : List (Nat × Nat) × Nat =>
    (p.1.findSome? (fun q => if q.1 = q.2 then some q.1 else none),
      p.1.countP (fun q => q.1 < q.2 + p.2), p.1.all (fun q => q.1 < q.2),
      p.1.find? (fun q => q.1 < q.2), p.1.lookup p.2)) := by fun_prop
example : PT (fun p : List Nat × List Nat =>
    (p.1.count 3, p.1.idxOf 2, p.1.erase 4, p.1.insert 3, p.1.removeAll p.2,
      (p.1 ++ p.2).eraseDups)) := by fun_prop
example : PT (fun p : Nat × List Nat =>
    (p.2.head!, p.2.max?, p.2.min?, p.2.foldl min p.1, p.2.zipIdx.map (fun (x, i) => x + i))) := by
  fun_prop
example : PT (fun l : List (List (List Nat)) =>
    l.flatten.map (fun t => (t.sum, t.reverse.head?))) := by fun_prop
example (g : Nat → Nat → Bool) (hg : PT (fun p : Nat × Nat => g p.1 p.2)) :
    PT (fun p : List Nat × Nat => (p.1.filter (g p.2), p.1.any (fun x => g x x))) := by fun_prop
/-- A nested program: for every clause, the list of positions of the clauses sharing a
variable with it. -/
example : PT (fun f : SAT.CNF => f.map (fun c =>
    (f.zipIdx.filter (fun q => q.1.any (fun l => c.any (fun l' => l.var == l'.var)))).map
      (·.2))) := by fun_prop

/-! ### Equality and membership -/

example : PT (fun p : Nat × Nat => (p.1 == p.2, decide (p.1 = p.2), p.1 != p.2)) := by fun_prop
example : PT (fun p : Bool × Bool => (p.1 == p.2, decide (p.1 = p.2), decide (p.1 = true))) := by
  fun_prop
example : PT (fun p : (Nat × Bool) × (Nat × Bool) => (p.1 == p.2, decide (p.1 = p.2))) := by
  fun_prop
example : PT (fun p : Option Nat × Option Nat =>
    (p.1 == p.2, decide (p.1 = p.2), decide (p.1 = none))) := by fun_prop
example : PT (fun p : List (Option Nat) × List (Option Nat) =>
    (p.1 == p.2, decide (p.1 = p.2), decide (p.1 ≠ []))) := by fun_prop
example : PT (fun p : SAT.Literal × SAT.Literal => (decide (p.1 = p.2), p.1 == p.2)) := by
  fun_prop
example : PT (fun p : SAT.CNF × SAT.CNF =>
    (p.1 == p.2, p.1 != p.2, decide (p.1 ≠ p.2), decide (p.1 = []))) := by fun_prop
example : PT (fun p : SAT.Literal × SAT.CNF =>
    (decide (∃ c ∈ p.2, p.1 ∈ c), p.2.map (fun c => c.contains p.1), p.2.flatten.elem p.1)) := by
  fun_prop
example : PT (fun p : List Nat × List Nat =>
    (decide (∀ x ∈ p.1, x ∈ p.2 ∨ x = 3), decide (∃ x ∈ p.1, x + 1 ∉ p.2),
      decide (p.1 ⊆ p.2))) := by fun_prop
example [DecidableEq (Nat ⊕ Bool)] : PT (fun p : (Nat ⊕ Bool) × List (Nat ⊕ Bool) =>
    (decide (p.2.head? = some p.1), p.2.any (fun x => decide (x = p.1)))) := by fun_prop
example {β : Type} [Code β] [DecidableEq β] : PT (fun p : β × List β =>
    (p.2.contains p.1, decide (p.1 ∈ p.2), p.2.idxOf p.1, p.2.eraseDups)) := by fun_prop
example {β : Type} [Code β] [BEq β] [LawfulBEq β] : PT (fun p : β × List (β × Nat) =>
    (p.2.lookup p.1, p.2.map (fun q => q.1 != p.1))) := by fun_prop

/-! ### Numbers and words -/

example (B : Nat) : PT (fun n : Nat => 2 ^ (B * Nat.log2 (n + 2))) := by fun_prop
example (B : Nat) : PT (fun p : Nat × Nat =>
    (2 ^ (Nat.log2 p.1 * B), 2 ^ Nat.log2 (p.1 * p.2), Nat.log2 p.2, (p.1 == p.2).toNat)) := by
  fun_prop
example (c : Nat) : PT (fun x : Word => allWords (c * Nat.log2 (x.length + 2))) := by fun_prop
example : PT (fun x : Word => (allWords (Nat.log2 x.length), natBits x.length,
    unary (x.length * 2))) := by fun_prop

/-- A bounded power: the bound is discharged with `two_pow_log2_le`. -/
example : PT (fun p : Nat × Nat => 2 ^ min p.1 (Nat.log2 p.2)) := by
  refine PT.two_pow_of_le (by fun_prop) (fun N => N) PolynomialBound.identity fun p => ?_
  have h1 : 2 ^ min p.1 (Nat.log2 p.2) ≤ 2 ^ Nat.log2 p.2 :=
    Nat.pow_le_pow_right (by omega) (Nat.min_le_right _ _)
  have h2 := two_pow_log2_le p.2
  simp only [size_prod, size_nat]
  omega

/-- The value of a logarithmically short binary numeral (most significant digit first). -/
example : PT (fun w : Word =>
    (w.take (Nat.log2 w.length)).foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0) := by
  refine PT.binValue_foldl (w := fun w : Word => w.take (Nat.log2 w.length)) (by fun_prop)
    (fun N => N) PolynomialBound.identity fun w => ?_
  have h1 : 2 ^ (w.take (Nat.log2 w.length)).length ≤ 2 ^ Nat.log2 w.length :=
    Nat.pow_le_pow_right (by omega) (List.length_take_le _ _)
  have h2 := two_pow_log2_le w.length
  have h3 := size_word w
  omega

/-- Binary digits and back (least significant digit first). -/
example : PT (fun n : Nat => SAT.binaryValue (natBits n)) :=
  (PT.id (α := Nat)).of_eq fun n => (binaryValue_natBits n).symm

/-- All words of a length whose power of two is bounded by the input. -/
example : PT (fun l : List Unit => allWords (Nat.log2 l.length)) := by
  refine PT.allWords (by fun_prop) (fun N => N) PolynomialBound.identity fun l => ?_
  have h1 := two_pow_log2_le l.length
  have h2 := length_lt_size l
  omega

/-! ### SAT -/

example : PT (fun p : Word × SAT.CNF =>
    decide (2 * SAT.satCount (SAT.assignmentOf p.1) p.2 ≥ p.2.length)) := by fun_prop
example : PT (fun p : Word × SAT.CNF => (SAT.evalCNF (SAT.assignmentOf p.1) p.2,
    p.2.map (SAT.evalClause (SAT.assignmentOf p.1)))) := by fun_prop
example : PT (fun p : Word × SAT.CNF =>
    p.2.map (fun c => c.map (fun l => SAT.evalLiteral (SAT.assignmentOf p.1) l))) := by fun_prop
/-- An assignment given by the list of the true variables. -/
example : PT (fun p : List Nat × SAT.CNF => SAT.evalCNF (fun i => decide (i ∈ p.1)) p.2) := by
  fun_prop
example : PT (fun f : SAT.CNF => f.length) := by fun_prop
example : PT (fun f : SAT.CNF => (Code.enc f : Word).length) := by fun_prop
example : PT (fun f : SAT.CNF => (size f, SAT.encode f, SAT.variableBound f,
    decide (∀ c ∈ f, c.length ≤ 3))) := by fun_prop
/-- Counting the random strings on which a formula-valued test accepts, as in `InPCP`. -/
example (c : Nat) : PT (fun p : Word × SAT.CNF =>
    (allWords (c * Nat.log2 (p.1.length + 2))).countP
      (fun r => SAT.evalCNF (SAT.assignmentOf (r ++ p.1)) p.2)) := by fun_prop
/-- Exhaustive search over the assignments to logarithmically many variables. -/
example : PT (fun f : SAT.CNF =>
    (allWords (Nat.log2 f.length)).find? (fun y => SAT.evalCNF (SAT.assignmentOf y) f)) := by
  fun_prop

/-! ### `match` -/

example : PT (fun p : List Nat × Nat =>
    match p.1.zipIdx.find? (fun q => q.1 == p.2) with
    | none => p.1.length
    | some q => q.2) := by
  refine PT.of_optionCases (o := fun p : List Nat × Nat => p.1.zipIdx.find? (fun q => q.1 == p.2))
    (d := fun p => p.1.length) (f := fun _ q => q.2) (by fun_prop) (by fun_prop) (by fun_prop)
    ?_ ?_
  · intro p h; simp only [h]
  · intro p b h; simp only [h]

/-! ### Recursion on a list -/

/-- Remove adjacent duplicates. -/
def dedupAdj : List Nat → List Nat
  | [] => []
  | x :: xs => if xs.head? = some x then dedupAdj xs else x :: dedupAdj xs

theorem dedupAdj_sublist (l : List Nat) : (dedupAdj l).Sublist l := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons x xs ih =>
    rw [dedupAdj]
    split
    · exact ih.cons _
    · exact ih.cons_cons _

/-- Structural recursion with `PT.of_listRec`; the values on suffixes are sublists of the
input, hence no larger. -/
example : PT dedupAdj := by
  refine PT.of_listRec (g := fun _ t => dedupAdj t) (base := fun _ => [])
    (step := fun _ x xs r => if xs.head? = some x then r else x :: r) (l := fun l => l)
    (by fun_prop) (by fun_prop) (by fun_prop) (fun _ => rfl) (fun _ _ _ => rfl)
    (fun N => N) PolynomialBound.identity ?_
  intro l suf hsuf
  exact Nat.le_trans (size_le_of_sublist (dedupAdj_sublist suf))
    (size_le_of_sublist hsuf.sublist)

/-- A fold whose accumulator grows additively (`PT.foldl_of_add_le`): the number of even
entries and the sum of the odd entries. -/
example : PT (fun l : List Nat => l.foldl
    (fun (acc : Nat × Nat) x => if x % 2 = 0 then (acc.1 + 1, acc.2) else (acc.1, acc.2 + x))
    (0, 0)) := by
  refine PT.foldl_of_add_le
    (f := fun _ (acc : Nat × Nat) x => if x % 2 = 0 then (acc.1 + 1, acc.2) else (acc.1, acc.2 + x))
    (init := fun _ => (0, 0)) (l := fun l => l) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun N => N) PolynomialBound.identity ?_
  intro l s x hx
  have h := size_le_of_mem hx
  split <;> simp only [size_prod, size_nat] at * <;> omega

/-- A fold with a bounded accumulator (`PT.foldl_of_size_le`): the parity of the length
together with the last entry. -/
example : PT (fun l : List Nat =>
    l.foldl (fun (acc : Bool × Nat) x => (!acc.1, x)) (false, 0)) := by
  refine PT.foldl_of_size_le (f := fun _ (acc : Bool × Nat) x => (!acc.1, x))
    (init := fun _ => (false, 0)) (l := fun l => l) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun N => N + 1) (PolynomialBound.identity.add (PolynomialBound.constant 1)) ?_
  intro l s x hx
  have h := size_le_of_mem hx
  simp only [size_prod, size_bool, size_nat] at *
  omega

/-! ### Raw words -/

/-- A CNF evaluator on `pairWords (encode f) y`. -/
example : ∃ G : Word → Word, PolyTime G ∧ ∀ (f : SAT.CNF) (y : Word),
    G (pairWords (SAT.encode f) y) =
      if SAT.evalCNF (SAT.assignmentOf y) f then [true] else [false] :=
  PT.exists_polyTime_pairWords_raw_bool
    (f := fun (f : SAT.CNF) (y : Word) => SAT.evalCNF (SAT.assignmentOf y) f) (by fun_prop)

/-- A formula transformation with a raw-word parameter. -/
example : ∃ G : Word → Word, PolyTime G ∧ ∀ (f : SAT.CNF) (y : Word),
    G (pairWords (SAT.encode f) y) =
      SAT.encode (f.filter (fun c => !SAT.evalClause (SAT.assignmentOf y) c)) :=
  PT.exists_polyTime_pairWords_raw
    (h := fun (f : SAT.CNF) (y : Word) =>
      f.filter (fun c => !SAT.evalClause (SAT.assignmentOf y) c)) (by fun_prop)

/-- A word-valued function of two coded arguments. -/
example : ∃ G : Word → Word, PolyTime G ∧ ∀ (f : SAT.CNF) (n : Nat),
    G (pairWords (SAT.encode f) (Code.enc n)) = (natBits (f.length + n)).reverse :=
  PT.exists_polyTime_pairWords_word
    (h := fun (f : SAT.CNF) (n : Nat) => (natBits (f.length + n)).reverse) (by fun_prop)

/-- A characteristic function on raw words, and a language in P. -/
example : PolyTime (fun x : Word => if x.count true = x.count false then [true] else [false]) :=
  polyTime_congr (fun x => by simp)
    (PT.polyTime_bool (f := fun x : Word => decide (x.count true = x.count false)) (by fun_prop))

example : PolyTime (fun z : Word =>
    if (Reg.unpair z).1.reverse == (Reg.unpair z).2 then [true] else [false]) :=
  PT.polyTime_bool_pairWords (f := fun x w : Word => x.reverse == w) (by fun_prop)

end Complexity.PT.Examples
