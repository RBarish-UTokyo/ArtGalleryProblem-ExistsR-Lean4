module

public import Complexity.PCP.Defs

/-!
# Optimization problems, approximation, MaxSNP and APX

Optimization problems on binary words, approximation algorithms and schemes, L-reductions and
the class MaxSNP of Papadimitriou and Yannakakis, PTAS-reductions and the class APX, and the
problems MAX-3-SAT and 3-OCCURRENCE MAX-3-SAT.
-/

@[expose] public section

namespace Complexity

/-- An optimization problem on binary words. `Sol x y v` says that `y` is a feasible
solution of the instance `x`, with value `v`; the goal is to maximize the value if `maximize`
is `true` and to minimize it otherwise. Words that are not instances have no solutions. -/
structure OptProblem where
  maximize : Bool
  Sol : Word → Word → Nat → Prop

namespace OptProblem

/-- `v` is the optimum of the instance `x`: the value of some solution, and no solution is
better. -/
def IsOpt (P : OptProblem) (x : Word) (v : Nat) : Prop :=
  (∃ y, P.Sol x y v) ∧
    ∀ y v', P.Sol x y v' → (P.maximize = true → v' ≤ v) ∧ (P.maximize = false → v ≤ v')

/-- A solution of value `v` is within the factor `a / b` of the optimum `opt`:
`opt ≤ (a / b) * v` for maximization, `v ≤ (a / b) * opt` for minimization. -/
def WithinRatio (P : OptProblem) (a b opt v : Nat) : Prop :=
  (P.maximize = true → b * opt ≤ a * v) ∧ (P.maximize = false → b * v ≤ a * opt)

/-- `A` is a polynomial-time approximation algorithm with ratio `a / b`: on every instance
that has an optimum it returns a solution within that factor of the optimum. -/
def ApproxAlgorithm (P : OptProblem) (a b : Nat) (A : Word → Word) : Prop :=
  PolyTime A ∧ ∀ x opt, P.IsOpt x opt → ∃ v, P.Sol x (A x) v ∧ P.WithinRatio a b opt v

/-- `P` has a polynomial-time approximation algorithm with ratio `a / b`. -/
def ApproximableWithin (P : OptProblem) (a b : Nat) : Prop :=
  ∃ A, P.ApproxAlgorithm a b A

end OptProblem

/-- The natural number `k` in unary: `k` ones. -/
def unary (k : Nat) : Word := List.replicate k true

/-- One machine computes `F k x` from `pairWords (unary k) x`, in time polynomial in `|x|`
for every fixed `k` (the polynomial may depend on `k`). -/
def UniformPolyTime (F : Nat → Word → Word) : Prop :=
  ∃ M : Machine, ∀ k, ∃ coefficient exponent, ∀ x : Word,
    ∃ time tape,
      time ≤ powerBound coefficient exponent x.length ∧
      runInput M time (pairWords (unary k) x) = some (true, tape) ∧
      tape.output = F k x

/-- `c` is computable: one machine maps `unary k` to `unary (c k)` (no time bound). -/
def ComputableNat (c : Nat → Nat) : Prop :=
  ∃ M : Machine, ∀ k, ∃ time tape,
    runInput M time (unary k) = some (true, tape) ∧ tape.output = unary (c k)

namespace OptProblem

/-- A polynomial-time approximation scheme: an algorithm that, for every `k`, returns
solutions within the factor `1 + 1 / (k + 1)` of the optimum, in time polynomial in the
instance for every fixed `k`. -/
def HasPTAS (P : OptProblem) : Prop :=
  ∃ A : Nat → Word → Word, UniformPolyTime A ∧
    ∀ k x opt, P.IsOpt x opt → ∃ v, P.Sol x (A k x) v ∧ P.WithinRatio (k + 2) (k + 1) opt v

end OptProblem

/-- The binary digits of `n`, least significant first (`natBitsFuel n n` has no leading zero
and is empty for `0`). -/
def natBitsFuel : Nat → Nat → Word
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else decide (n % 2 = 1) :: natBitsFuel fuel (n / 2)

/-- The natural number `n` in binary, least significant digit first. -/
def natBits (n : Nat) : Word := natBitsFuel n n

/-- NPO: solutions are polynomially bounded, and one polynomial-time function decides
feasibility and computes the value (in binary): it maps `pairWords x y` to
`true :: natBits v` exactly when `y` is a solution of `x` of value `v`. -/
def NPO (P : OptProblem) : Prop :=
  (∃ coefficient exponent, ∀ x y v, P.Sol x y v →
    y.length ≤ powerBound coefficient exponent x.length) ∧
  ∃ F : Word → Word, PolyTime F ∧
    ∀ x y v, P.Sol x y v ↔ F (pairWords x y) = true :: natBits v

/-- `|a - b|` for natural numbers. -/
def absDiff (a b : Nat) : Nat := (a - b) + (b - a)

/-- L-reducibility (Papadimitriou–Yannakakis): polynomial-time `f` on instances and `g` on
solutions (given `pairWords x y`), and constants `α`, `β`, such that, for every instance `x`
of `P` with optimum `opt`: `f x` has an optimum `opt' ≤ α * opt`, and every solution `y` of
`f x`, of value `v'`, is mapped to a solution of `x` of value `v` with
`|opt - v| ≤ β * |opt' - v'|`. -/
def LReducible (P Q : OptProblem) : Prop :=
  ∃ (f g : Word → Word) (α β : Nat), PolyTime f ∧ PolyTime g ∧
    ∀ x opt, P.IsOpt x opt →
      ∃ opt', Q.IsOpt (f x) opt' ∧ opt' ≤ α * opt ∧
        ∀ y v', Q.Sol (f x) y v' →
          ∃ v, P.Sol x (g (pairWords x y)) v ∧ absDiff opt v ≤ β * absDiff opt' v'

/-- Quantifier-free first-order formulas `φ(x₀, …, x_{k-1}; G, S)`: atoms apply an input
relation `G_rel` or a solution relation `S_rel` to the variables listed in `args`, or compare
two variables. -/
inductive QF where
  | input (rel : Nat) (args : List Nat)
  | sol (rel : Nat) (args : List Nat)
  | eq (i j : Nat)
  | not (φ : QF)
  | and (φ ψ : QF)
  | or (φ ψ : QF)

/-- Finitely many finite relations on natural numbers: the `i`-th list holds the tuples of
the `i`-th relation. -/
abbrev Relations := List (List (List Nat))

/-- The tuple `t` belongs to the `i`-th relation. -/
def Relations.holds (R : Relations) (i : Nat) (t : List Nat) : Bool :=
  (R.getD i []).any fun u => decide (u = t)

/-- The truth value of a quantifier-free formula at the tuple `x`, for input relations `G`
and solution relations `S`. -/
def QF.eval (G S : Relations) (x : List Nat) : QF → Bool
  | .input rel args => G.holds rel (args.map fun i => x.getD i 0)
  | .sol rel args => S.holds rel (args.map fun i => x.getD i 0)
  | .eq i j => decide (x.getD i 0 = x.getD j 0)
  | .not φ => !(φ.eval G S x)
  | .and φ ψ => φ.eval G S x && ψ.eval G S x
  | .or φ ψ => φ.eval G S x || ψ.eval G S x

/-- The tuples of length `k` over the universe `{0, …, n - 1}`, each once. -/
def tuples (n k : Nat) : List (List Nat) :=
  Nat.repeat (fun ts => ts.flatMap fun t => (List.range n).map fun a => a :: t) k [[]]

@[simp] theorem tuples_zero (n : Nat) : tuples n 0 = [[]] := rfl

theorem tuples_succ (n k : Nat) :
    tuples n (k + 1) = (tuples n k).flatMap fun t => (List.range n).map fun a => a :: t := rfl

/-- The code of a family of relations (lists coded as in `SAT.writeList`, numbers in unary). -/
def encodeRelations (R : Relations) : Word :=
  SAT.writeList (SAT.writeList (SAT.writeList SAT.writeNat)) R

/-- `R` is a structure of the signature `ar` over the universe `{0, …, n - 1}`: it has one
relation for each arity in `ar`, and the relation of arity `a` lists distinct `a`-tuples of
elements of the universe. -/
def Relations.Fits (R : Relations) (n : Nat) (ar : List Nat) : Prop :=
  R.length = ar.length ∧
    ∀ p ∈ R.zip ar, p.1.Nodup ∧ ∀ t ∈ p.1, t.length = p.2 ∧ ∀ a ∈ t, a < n

/-- `φ` is a formula in the variables `x₀, …, x_{k-1}` over input relations with the arities
`ga` and solution relations with the arities `sa`: every atom applies a relation of the
signature to as many variables as its arity, and every variable index is below `k`. -/
def QF.WellFormed (ga sa : List Nat) (k : Nat) : QF → Prop
  | .input rel args => ga[rel]? = some args.length ∧ ∀ i ∈ args, i < k
  | .sol rel args => sa[rel]? = some args.length ∧ ∀ i ∈ args, i < k
  | .eq i j => i < k ∧ j < k
  | .not φ => φ.WellFormed ga sa k
  | .and φ ψ => φ.WellFormed ga sa k ∧ ψ.WellFormed ga sa k
  | .or φ ψ => φ.WellFormed ga sa k ∧ ψ.WellFormed ga sa k

/-- The syntactic class MaxSNP₀: for the input signature `ga`, the solution signature `sa`
and a quantifier-free formula `φ` in `k` variables, the instances are finite structures of
signature `ga` (a universe `{0, …, n - 1}` and input relations `G`), the solutions are
structures `S` of signature `sa` over the same universe, and the value to maximize is the
number of `k`-tuples `x` of the universe with `φ(x; G, S)`. -/
def maxSNP0 (ga sa : List Nat) (k : Nat) (φ : QF) : OptProblem where
  maximize := true
  Sol x y v := ∃ (n : Nat) (G S : Relations), G.Fits n ga ∧ S.Fits n sa ∧
    x = SAT.writeNat n ++ encodeRelations G ∧ y = encodeRelations S ∧
    v = (tuples n k).countP fun t => φ.eval G S t

/-- MaxSNP: the NPO problems L-reducible to a problem of the syntactic class given by a
well-formed formula. -/
def InMaxSNP (P : OptProblem) : Prop :=
  NPO P ∧ ∃ ga sa k φ, QF.WellFormed ga sa k φ ∧ LReducible P (maxSNP0 ga sa k φ)

/-- `P` is MaxSNP-hard: every problem of MaxSNP is L-reducible to `P`. -/
def MaxSNPHard (P : OptProblem) : Prop :=
  ∀ Q, InMaxSNP Q → LReducible Q P

/-- `P` is MaxSNP-complete. -/
def MaxSNPComplete (P : OptProblem) : Prop :=
  InMaxSNP P ∧ MaxSNPHard P

/-- MAX-3-SAT: the instances are the codes of 3-CNF formulas, a solution is a truth
assignment written as a word no longer than the instance (variables beyond its end are false;
every variable of the formula has an index below the length of the instance, because indices
are written in unary), and the value to maximize is the number of satisfied clauses. -/
def max3SAT : OptProblem where
  maximize := true
  Sol x y v := ∃ f, SAT.encode f = x ∧ SAT.IsThreeCNF f ∧ y.length ≤ x.length ∧
    v = SAT.satCount (SAT.assignmentOf y) f

/-- The number of occurrences of the variable `v` in `f`. -/
def SAT.occurrences (f : SAT.CNF) (v : Nat) : Nat :=
  f.flatten.countP fun l => Nat.beq l.var v

/-- Every variable occurs at most three times in `f`. -/
def SAT.IsThreeOcc (f : SAT.CNF) : Prop :=
  ∀ v, SAT.occurrences f v ≤ 3

/-- 3-OCCURRENCE MAX-3-SAT: MAX-3-SAT restricted to formulas in which every variable occurs
at most three times. -/
def max3SAT3 : OptProblem where
  maximize := true
  Sol x y v := ∃ f, SAT.encode f = x ∧ SAT.IsThreeCNF f ∧ SAT.IsThreeOcc f ∧
    y.length ≤ x.length ∧ v = SAT.satCount (SAT.assignmentOf y) f

/-- APX: the NPO problems with a polynomial-time approximation algorithm of constant ratio. -/
def InAPX (P : OptProblem) : Prop :=
  NPO P ∧ ∃ a b, 0 < b ∧ P.ApproximableWithin a b

/-- PTAS-reducibility (Crescenzi–Trevisan), with precisions `1 / (k + 1)`: `f k` maps
instances and `g k` maps solutions back (given `pairWords x y`), both in time polynomial for
every fixed `k`, and `c` is computable, such that for every instance `x` of `P` with an
optimum: `f k x` has an optimum, every solution `y` of `f k x` is mapped to a solution of
`x`, and if `y` is within `1 + 1 / (c k + 1)` of the optimum of `f k x` then its image is
within `1 + 1 / (k + 1)` of the optimum of `x`. -/
def PTASReducible (P Q : OptProblem) : Prop :=
  ∃ (f g : Nat → Word → Word) (c : Nat → Nat),
    UniformPolyTime f ∧ UniformPolyTime g ∧ ComputableNat c ∧
    ∀ k x opt, P.IsOpt x opt →
      ∃ opt', Q.IsOpt (f k x) opt' ∧
        ∀ y v', Q.Sol (f k x) y v' →
          ∃ v, P.Sol x (g k (pairWords x y)) v ∧
            (Q.WithinRatio (c k + 2) (c k + 1) opt' v' → P.WithinRatio (k + 2) (k + 1) opt v)

/-- `P` is APX-hard: every problem of APX is PTAS-reducible to `P`. -/
def APXHard (P : OptProblem) : Prop :=
  ∀ Q, InAPX Q → PTASReducible Q P

/-- `P` is APX-complete. -/
def APXComplete (P : OptProblem) : Prop :=
  InAPX P ∧ APXHard P

end Complexity
