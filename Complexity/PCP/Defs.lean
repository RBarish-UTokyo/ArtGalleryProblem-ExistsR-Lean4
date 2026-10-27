module

public import Complexity.Classes
public import Complexity.SAT

/-!
# Statements about probabilistically checkable proofs

Definitions for the PCP theorem in its two usual forms: hardness of the gap version of
3-SAT, and the characterisation `NP = PCP(O(log n), O(1))` by verifiers.
-/

@[expose] public section

namespace Complexity

/-- `P = NP`: every language in NP is decided by a polynomial-time machine. -/
def PEqNP : Prop := ∀ L : Language, InNP L → InP L

namespace SAT

/-- The number of clauses of `f` that the assignment `a` satisfies. -/
def satCount (a : Assignment) (f : CNF) : Nat :=
  f.countP (evalClause a)

/-- The assignment written by a word: variable `i` gets the `i`-th bit, and `false` beyond the
end of the word. -/
def assignmentOf (y : Word) : Assignment :=
  fun i => y.getD i false

end SAT

/-- The binary words of length `n`, each once. -/
def allWords (n : Nat) : List Word :=
  Nat.repeat (fun ws => ws.flatMap fun w => [false :: w, true :: w]) n [[]]

@[simp] theorem allWords_zero : allWords 0 = [[]] := rfl

theorem allWords_succ (n : Nat) :
    allWords (n + 1) = (allWords n).flatMap fun w => [false :: w, true :: w] := rfl

/-- The formula `f` mentions at most `q` distinct variables. -/
def QueriesAtMost (q : Nat) (f : SAT.CNF) : Prop :=
  ∃ vars : List Nat, vars.length ≤ q ∧ ∀ c ∈ f, ∀ l ∈ c, l.var ∈ vars

/-- `L ∈ PCP(c log n, q)`. A (non-adaptive) verifier is a polynomial-time `V` that maps the
input `x` and a random string `r` (given as `pairWords x r`) to a CNF formula over the bits of
the proof: the proof `π` is accepted when it satisfies `V (pairWords x r)`. The random strings
are the words of length `c * Nat.log2 (|x| + 2)`; every formula mentions at most `q` proof
bits. Members have a proof accepted for every random string; for non-members every proof is
accepted for at most half of the random strings. -/
def InPCP (c q : Nat) (L : Language) : Prop :=
  ∃ V : Word → SAT.CNF, PolyTime (fun w => SAT.encode (V w)) ∧
    ∀ x : Word,
      (∀ r ∈ allWords (c * Nat.log2 (x.length + 2)), QueriesAtMost q (V (pairWords x r))) ∧
      (L x → ∃ proof : SAT.Assignment,
        ∀ r ∈ allWords (c * Nat.log2 (x.length + 2)),
          SAT.evalCNF proof (V (pairWords x r)) = true) ∧
      (¬ L x → ∀ proof : SAT.Assignment,
        2 * ((allWords (c * Nat.log2 (x.length + 2))).countP fun r =>
            SAT.evalCNF proof (V (pairWords x r))) ≤
          (allWords (c * Nat.log2 (x.length + 2))).length)

/-- `g` is a gap reduction from `L` to 3-SAT with gap `num / den`: it is computable in
polynomial time, its formulas are nonempty 3-CNF formulas, members of `L` give satisfiable
formulas, and for non-members every assignment leaves at least the fraction `num / den` of
the clauses unsatisfied. -/
def GapReduction (num den : Nat) (L : Language) (g : Word → SAT.CNF) : Prop :=
  PolyTime (fun x => SAT.encode (g x)) ∧
    ∀ x, SAT.IsThreeCNF (g x) ∧ g x ≠ [] ∧
      (L x → SAT.Satisfiable (g x)) ∧
      (¬ L x → ∀ a : SAT.Assignment,
        den * SAT.satCount a (g x) + num * (g x).length ≤ den * (g x).length)

end Complexity
