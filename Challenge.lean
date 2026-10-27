module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Finset.Card
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.RingTheory.Algebraic.Defs

/-!
# The art gallery problem is ∃ℝ-complete — statement

This file is the statement a reader audits.  It consists of the definitions of
`ArtGallery/Spec.lean` (the specification inside the library) and of the machine model of
`Complexity/Machine.lean` and `Complexity/Classes.lean`, followed by the theorem statements; `Solution.lean` proves the same theorems
without importing it, and `lake comparator` checks that the two agree.

Source: M. Abrahamsen, A. Adamaszek, T. Miltzow, *The Art Gallery Problem is ∃ℝ-complete*,
J. ACM 69(1), Article 4 (2021).  See the module documentation of `ArtGallery/Spec.lean` (repeated
in the sections below) for the conventions.
-/

@[expose] public section

namespace Complexity

/-- Tape symbols: the blank, the two bits, and a separator `sep` (a work symbol). -/
inductive Symbol where
  | blank | bit (value : Bool) | sep

/-- A head movement: one cell left, none, or one cell right. -/
inductive Move where
  | left | stay | right

/-- A two-way infinite tape: `right` is the scanned cell and the cells to its right,
`left` the cells to its left, nearest first; all other cells are blank. -/
structure Tape where
  left : List Symbol
  right : List Symbol

namespace Tape

/-- The scanned symbol (blank beyond the stored cells). -/
def read (t : Tape) : Symbol := t.right.headD .blank

/-- Overwrite the scanned cell with `a`. -/
def write (a : Symbol) (t : Tape) : Tape :=
  { t with right := a :: t.right.drop 1 }

/-- Move the head by `d`, storing a blank cell when it moves past the stored cells. -/
def move (d : Move) (t : Tape) : Tape :=
  match d with
  | .stay => t
  | .left =>
    match t.left with
    | [] => ⟨[], .blank :: t.right⟩
    | a :: rest => ⟨rest, a :: t.right⟩
  | .right =>
    match t.right with
    | [] => ⟨.blank :: t.left, []⟩
    | a :: rest => ⟨a :: t.left, rest⟩

/-- The tape holding `input` as bits, head on its first cell, blank elsewhere. -/
def ofInput (input : List Bool) : Tape := ⟨[], input.map Symbol.bit⟩

/-- The longest prefix of a symbol list made of bits, as a binary word. -/
def bits : List Symbol → List Bool
  | .bit b :: rest => b :: bits rest
  | _ => []

/-- The output: the bits from the head rightwards, up to the first non-bit cell. -/
def output (t : Tape) : List Bool := bits t.right

end Tape

/-- An instruction: `halt b` (`true` accepts), or write, move, and enter state `next`. -/
inductive Instruction (states : Nat) where
  | halt (decision : Bool)
  | step (write : Symbol) (move : Move) (next : Fin states)

/-- A deterministic single-tape Turing machine: control states `Fin (states + 1)`,
a start state, and an instruction for every control state and scanned symbol. -/
structure Machine where
  states : Nat
  start : Fin (states + 1)
  code : Fin (states + 1) → Symbol → Instruction (states + 1)

/-- A configuration of `M`: control state and tape (with head). -/
structure Config (M : Machine) where
  state : Fin (M.states + 1)
  tape : Tape

/-- The initial configuration on `input`: start state, input tape (`Tape.ofInput`). -/
def initial (M : Machine) (input : List Bool) : Config M :=
  ⟨M.start, Tape.ofInput input⟩

/-- One step from `c`: `.inl (b, tape)` on `halt b`, else the next configuration. -/
def step (M : Machine) (c : Config M) : (Bool × Tape) ⊕ Config M :=
  match M.code c.state c.tape.read with
  | .halt b => .inl (b, c.tape)
  | .step a d q => .inr ⟨q, (c.tape.write a).move d⟩

/-- `run M fuel c` executes at most `fuel` steps from `c`. It is `some (b, t)` if
the machine executes `halt b` within these steps (halting counts as a step),
`t` being the final tape, and `none` if it has not halted after `fuel` steps. -/
def run (M : Machine) : Nat → Config M → Option (Bool × Tape)
  | 0, _ => none
  | fuel + 1, c =>
    match M.code c.state c.tape.read with
    | .halt b => some (b, c.tape)
    | .step a d q => run M fuel ⟨q, (c.tape.write a).move d⟩

/-- `run` from the initial configuration on `input`. -/
def runInput (M : Machine) (fuel : Nat) (input : List Bool) :
    Option (Bool × Tape) := run M fuel (initial M input)

/-- Binary words. -/
abbrev Word := List Bool
/-- A language (decision problem): a set of binary words. -/
abbrev Language := Word → Prop

/-- The bound `c * (n + 1) ^ k`. Every polynomial in `n` with natural coefficients
is at most such a bound, so these bounds express polynomial time and length.
`Nat.pow` is written out so that this term is the same when Mathlib is imported. -/
def powerBound (coefficient exponent inputSize : Nat) : Nat :=
  coefficient * Nat.pow (inputSize + 1) exponent

/-- The pair `(x, y)` as one word, `|x|` ones, a zero, `x`, `y`: how NP verifiers get input. -/
def pairWords (x y : Word) : Word :=
  List.replicate x.length true ++ false :: (x ++ y)

/-- `M` accepts `input`: its run on `input` halts with decision `true`. -/
def Accepts (M : Machine) (input : Word) : Prop :=
  ∃ time tape, runInput M time input = some (true, tape)

/-- `M` halts, accepting or rejecting, within `c * (n + 1) ^ k` steps on every input. -/
def PolynomialTimeMachine (M : Machine) : Prop :=
  ∃ coefficient exponent, ∀ input : Word,
    ∃ time decision tape,
      time ≤ powerBound coefficient exponent input.length ∧
      runInput M time input = some (decision, tape)

/-- `f` is computable in polynomial time: one machine, on every input `x` of
length `n`, halts with decision `true` within `c * (n + 1) ^ k` steps, with
`f x` as the output (`Tape.output`) of its final tape. -/
def PolyTime (f : Word → Word) : Prop :=
  ∃ M : Machine, ∃ coefficient exponent, ∀ input : Word,
    ∃ time tape,
      time ≤ powerBound coefficient exponent input.length ∧
      runInput M time input = some (true, tape) ∧
      tape.output = f input

/-- Karp reducibility: a polynomial-time `f` with `x ∈ A ↔ f x ∈ B` for every word `x`. -/
def PolyRed (A B : Language) : Prop :=
  ∃ f : Word → Word, PolyTime f ∧ ∀ input, A input ↔ B (f input)

end Complexity

/-!
## Specification: the art gallery problem is ∃ℝ-complete

This file is the single authoritative statement of what is proved.  It contains every definition
used by the advertised theorems; `Challenge.lean` is a generated, self-contained copy of it (with
the machine model of `Complexity.Machine`/`Complexity.Classes` inlined) followed by the theorem
statements.  The source is

  M. Abrahamsen, A. Adamaszek, T. Miltzow, *The Art Gallery Problem is ∃ℝ-complete*,
  Journal of the ACM 69(1), Article 4 (2021).

## Conventions

* **Machines and polynomial time** are those of `Complexity.Machine` and `Complexity.Classes`
  (deterministic single-tape Turing machines over {blank, 0, 1, separator}; `PolyTime f`: one
  machine computes `f` within `c * (n + 1) ^ k` steps; `PolyRed A B`: a polynomial-time Karp
  reduction).  They are reused verbatim from the author's Palomar entries
  PALOMAR-2026-10-02-000013 and PALOMAR-2026-10-09-000010.
* **The existential theory of the reals.**  A formula is a quantifier-free formula of the
  first-order language of the reals with constants `0, 1`, the operations `+, −, ·`, the
  relations `=, <, ≤` and the connectives `¬, ∧, ∨`; its variables are `x₀, x₁, …`.  The
  sentence `∃ x₀ x₁ … φ` (all variables existentially quantified, i.e. prenex existential form)
  is true iff `φ` is satisfiable over `ℝ`.  `ETR` is the language of binary codes of formulas
  whose existential closure is true.  `∃ℝ` is the class of languages that reduce to `ETR` by
  polynomial-time many-one reductions.
* **Codes.**  Variable indices are written in unary; numbers occurring in art-gallery
  instances (numerators, denominators, the number of guards) are written in binary.
* **Polygons** are given by their vertex lists in boundary order (the definitions are those of
  the author's Palomar entry PALOMAR-2026-10-05-000003 on Chazelle's triangulation algorithm).
  A polygon is
  *simple* if it has at least three pairwise distinct vertices and any two distinct edges meet
  exactly in their common endpoints (collinear consecutive vertices are allowed).  The closed
  region `P.filled` is the boundary together with the points whose connected component in the
  complement of the boundary is bounded (for a simple polygon: the closed region enclosed by the
  boundary; the definition does not presuppose the Jordan curve theorem).
* **Guarding.**  Two points see each other if the closed segment joining them lies in the closed
  region.  A guard set is a set of points of the region such that every point of the region is
  seen by one of them.  The art gallery problem asks, for a simple polygon with rational vertex
  coordinates and a number `g`, whether the polygon has a guard set of cardinality `g`.
  In the *point-boundary* variant (`AGPPointBoundary`, Stade, SoCG 2025) only the boundary must be
  seen by the guards; in the *boundary-point* variant (`AGPBoundaryPoint`) the guards must lie on
  the boundary and see the whole region.
-/

namespace ArtGallery

open Complexity

/-! ## Binary codes -/

/-- `n` in unary: `n` ones followed by a zero. -/
def unary (n : ℕ) : Word := List.replicate n true ++ [false]

/-- `n` in binary: the number of binary digits in unary, then the digits of `n`, least
significant first (`Nat.bits`; `0` has no digits). -/
def binaryNat (n : ℕ) : Word := unary n.bits.length ++ n.bits

/-- An integer in binary: a sign bit (`true` for negative numbers), then its absolute value
in binary. -/
def binaryInt (z : ℤ) : Word := decide (z < 0) :: binaryNat z.natAbs

/-- A list, each entry preceded by `1`, terminated by `0`. -/
def encodeList {α : Type} (e : α → Word) : List α → Word
  | [] => [false]
  | a :: l => true :: (e a ++ encodeList e l)

/-! ## The existential theory of the reals -/

namespace ETR

/-- Terms of the first-order language of ordered rings: the variable `x i`, the constants
`0` and `1`, and the operations `+`, `−`, `·`. -/
inductive Term where
  | var (index : ℕ)
  | zero
  | one
  | add (s t : Term)
  | sub (s t : Term)
  | mul (s t : Term)

/-- Quantifier-free formulas: the atomic relations `=`, `<`, `≤` between terms, closed under
`¬`, `∧`, `∨`. -/
inductive Formula where
  | eq (s t : Term)
  | lt (s t : Term)
  | le (s t : Term)
  | not (φ : Formula)
  | and (φ ψ : Formula)
  | or (φ ψ : Formula)

/-- The value of a term under the assignment `x` of real numbers to the variables. -/
def Term.eval (x : ℕ → ℝ) : Term → ℝ
  | .var i => x i
  | .zero => 0
  | .one => 1
  | .add s t => s.eval x + t.eval x
  | .sub s t => s.eval x - t.eval x
  | .mul s t => s.eval x * t.eval x

/-- The formula holds under the assignment `x`. -/
def Formula.Holds (x : ℕ → ℝ) : Formula → Prop
  | .eq s t => s.eval x = t.eval x
  | .lt s t => s.eval x < t.eval x
  | .le s t => s.eval x ≤ t.eval x
  | .not φ => ¬ φ.Holds x
  | .and φ ψ => φ.Holds x ∧ ψ.Holds x
  | .or φ ψ => φ.Holds x ∨ ψ.Holds x

/-- The existential sentence `∃ x₀ x₁ …, φ` is true: some real assignment satisfies `φ`. -/
def Formula.Satisfiable (φ : Formula) : Prop := ∃ x : ℕ → ℝ, φ.Holds x

/-- Every variable of the term has index less than `n`. -/
def Term.VarsLt (n : ℕ) : Term → Prop
  | .var i => i < n
  | .zero => True
  | .one => True
  | .add s t => s.VarsLt n ∧ t.VarsLt n
  | .sub s t => s.VarsLt n ∧ t.VarsLt n
  | .mul s t => s.VarsLt n ∧ t.VarsLt n

/-- Every variable of the formula has index less than `n`. -/
def Formula.VarsLt (n : ℕ) : Formula → Prop
  | .eq s t => s.VarsLt n ∧ t.VarsLt n
  | .lt s t => s.VarsLt n ∧ t.VarsLt n
  | .le s t => s.VarsLt n ∧ t.VarsLt n
  | .not φ => φ.VarsLt n
  | .and φ ψ => φ.VarsLt n ∧ ψ.VarsLt n
  | .or φ ψ => φ.VarsLt n ∧ ψ.VarsLt n

/-- The binary code of a term, in prefix (Polish) notation: a three-bit tag, then the index
in unary (for a variable) or the codes of the two arguments. -/
def Term.encode : Term → Word
  | .var i => [false, false, false] ++ unary i
  | .zero => [false, false, true]
  | .one => [false, true, false]
  | .add s t => [false, true, true] ++ s.encode ++ t.encode
  | .sub s t => [true, false, false] ++ s.encode ++ t.encode
  | .mul s t => [true, false, true] ++ s.encode ++ t.encode

/-- The binary code of a formula, in prefix (Polish) notation: a three-bit tag, then the codes
of the arguments. -/
def Formula.encode : Formula → Word
  | .eq s t => [false, false, false] ++ s.encode ++ t.encode
  | .lt s t => [false, false, true] ++ s.encode ++ t.encode
  | .le s t => [false, true, false] ++ s.encode ++ t.encode
  | .not φ => [false, true, true] ++ φ.encode
  | .and φ ψ => [true, false, false] ++ φ.encode ++ ψ.encode
  | .or φ ψ => [true, false, true] ++ φ.encode ++ ψ.encode

end ETR

/-- **ETR**: the codes of the true sentences of the existential theory of the reals. -/
def ETR : Language := fun w => ∃ φ : ETR.Formula, φ.encode = w ∧ φ.Satisfiable

/-- `L` is in `∃ℝ`: it reduces to `ETR` by a polynomial-time many-one reduction. -/
def InER (L : Language) : Prop := PolyRed L ETR

/-- `L` is `∃ℝ`-hard: every language in `∃ℝ` reduces to `L` in polynomial time. -/
def ERHard (L : Language) : Prop := ∀ L' : Language, InER L' → PolyRed L' L

/-- `L` is `∃ℝ`-complete. -/
def ERComplete (L : Language) : Prop := InER L ∧ ERHard L

/-! ## ETR-INV (Definition 14) -/

namespace ETRINV

/-- An equation of ETR-INV: `x = 1`, `x + y = z` or `x · y = 1`, on the variables `x i`. -/
inductive Constraint where
  | one (x : ℕ)
  | add (x y z : ℕ)
  | inv (x y : ℕ)

/-- The equation holds under the assignment `v`. -/
def Constraint.Holds (v : ℕ → ℝ) : Constraint → Prop
  | .one x => v x = 1
  | .add x y z => v x + v y = v z
  | .inv x y => v x * v y = 1

/-- Every variable of the equation has index less than `n`. -/
def Constraint.VarsLt (n : ℕ) : Constraint → Prop
  | .one x => x < n
  | .add x y z => x < n ∧ y < n ∧ z < n
  | .inv x y => x < n ∧ y < n

/-- The binary code of an equation: a two-bit tag, then the variable indices in unary. -/
def Constraint.encode : Constraint → Word
  | .one x => [false, false] ++ unary x
  | .add x y z => [false, true] ++ unary x ++ unary y ++ unary z
  | .inv x y => [true, false] ++ unary x ++ unary y

/-- An instance (a list of equations) has a solution with every variable in `[1/2, 2]`. -/
def Satisfiable (Φ : List Constraint) : Prop :=
  ∃ v : ℕ → ℝ, (∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) ∧ ∀ c ∈ Φ, c.Holds v

/-- The binary code of an instance. -/
def encode (Φ : List Constraint) : Word := encodeList Constraint.encode Φ

end ETRINV

/-- **ETR-INV**: the codes of the solvable instances. -/
def ETRINV : Language := fun w => ∃ Φ : List ETRINV.Constraint, ETRINV.encode Φ = w ∧
  ETRINV.Satisfiable Φ

/-! ## Polygons -/

/-- A point of the plane. -/
abbrev Point : Type := ℝ × ℝ

/-- The closed segment from `a` to `b`. -/
def segment (a b : Point) : Set Point :=
  {p | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = (a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2))}

/-- A set of points is bounded when it lies in some square centred at the origin. -/
def IsBoundedSet (S : Set Point) : Prop :=
  ∃ R : ℝ, ∀ p ∈ S, |p.1| ≤ R ∧ |p.2| ≤ R

/-- A polygon: its vertices in boundary order. -/
structure Polygon where
  /-- The vertex list `v₀, v₁, …, vₙ₋₁`; edge `i` joins `vᵢ` to `v_{(i+1) mod n}`. -/
  vertices : List Point

namespace Polygon

variable (P : Polygon)

/-- The number of vertices `n`. -/
def n : ℕ := P.vertices.length

/-- Total vertex lookup: `vtx i` is the `i`-th vertex, or the origin if `i ≥ n`. -/
def vtx (i : ℕ) : Point := P.vertices.getD i (0, 0)

/-- Edge `i` is the closed segment from vertex `i` to vertex `(i+1) mod n`. -/
def edge (i : ℕ) : Set Point := segment (P.vtx i) (P.vtx ((i + 1) % P.n))

/-- The boundary: the union of all edges. -/
def boundary : Set Point := {p | ∃ i, i < P.n ∧ p ∈ P.edge i}

/-- The vertex points shared by edges `i` and `j`. -/
def commonEndpoints (i j : ℕ) : Set Point :=
  {p | (p = P.vtx i ∨ p = P.vtx ((i + 1) % P.n)) ∧ (p = P.vtx j ∨ p = P.vtx ((j + 1) % P.n))}

/-- The standard notion of a simple polygon: at least three vertices, pairwise
distinct, and any two distinct edges intersect exactly in their common
endpoints.  No general-position assumption is made. -/
def Simple : Prop :=
  3 ≤ P.n ∧
  (∀ i j, i < P.n → j < P.n → P.vtx i = P.vtx j → i = j) ∧
  (∀ i j, i < P.n → j < P.n → i ≠ j → P.edge i ∩ P.edge j = P.commonEndpoints i j)

/-- The closed region of the polygon: the boundary together with every point whose
connected component in the complement of the boundary is bounded. -/
def filled : Set Point :=
  P.boundary ∪ {p | IsBoundedSet (connectedComponentIn P.boundaryᶜ p)}

/-- `p` and `q` see each other: the closed segment `pq` lies in the closed region. -/
def Sees (p q : Point) : Prop := segment p q ⊆ P.filled

/-- `G` is a guard set: its points lie in the region, and every point of the region is seen by
some point of `G`. -/
def IsGuardSet (G : Set Point) : Prop :=
  G ⊆ P.filled ∧ ∀ p ∈ P.filled, ∃ g ∈ G, P.Sees g p

/-- The polygon has a guard set of cardinality `k`. -/
def HasGuardSetOfCard (k : ℕ) : Prop :=
  ∃ G : Finset Point, G.card = k ∧ P.IsGuardSet (G : Set Point)

/-- `G` guards the boundary: its points lie in the region, and every point of the boundary is
seen by some point of `G` (the *point-boundary* variant: guards anywhere in the region, only the
walls must be seen). -/
def IsBoundaryGuardSet (G : Set Point) : Prop :=
  G ⊆ P.filled ∧ ∀ p ∈ P.boundary, ∃ g ∈ G, P.Sees g p

/-- The polygon has a boundary guard set of cardinality `k`. -/
def HasBoundaryGuardSetOfCard (k : ℕ) : Prop :=
  ∃ G : Finset Point, G.card = k ∧ P.IsBoundaryGuardSet (G : Set Point)

/-- `G` is a guard set on the boundary: its points lie on the boundary, and every point of the
region is seen by some point of `G` (the *boundary-point* variant: guards on the walls, the whole
region must be seen). -/
def IsGuardSetOnBoundary (G : Set Point) : Prop :=
  G ⊆ P.boundary ∧ ∀ p ∈ P.filled, ∃ g ∈ G, P.Sees g p

/-- The polygon has a guard set on the boundary of cardinality `k`. -/
def HasGuardSetOnBoundaryOfCard (k : ℕ) : Prop :=
  ∃ G : Finset Point, G.card = k ∧ P.IsGuardSetOnBoundary (G : Set Point)

/-- `G` is an optimal guard set: a guard set of minimum cardinality. -/
def IsOptimalGuardSet (G : Finset Point) : Prop :=
  P.IsGuardSet (G : Set Point) ∧
    ∀ G' : Finset Point, P.IsGuardSet (G' : Set Point) → G.card ≤ G'.card

/-- The polygon is (x-)monotone: its intersection with every vertical line is connected. -/
def XMonotone : Prop := ∀ a : ℝ, IsPreconnected {p ∈ P.filled | p.1 = a}

end Polygon

/-- The point with rational coordinates `p`. -/
def ratPoint (p : ℚ × ℚ) : Point := ((p.1 : ℝ), (p.2 : ℝ))

/-- The point with integer coordinates `p`. -/
def intPoint (p : ℤ × ℤ) : Point := ((p.1 : ℝ), (p.2 : ℝ))

/-- A point with rational coordinates. -/
def IsRationalPoint (p : Point) : Prop := ∃ a b : ℚ, p = ((a : ℝ), (b : ℝ))

/-! ## The art gallery problem -/

/-- A vertex of an art-gallery instance: its coordinates as fractions `xNum / xDen` and
`yNum / yDen` of integers (not necessarily in lowest terms). -/
structure FracPoint where
  xNum : ℤ
  xDen : ℕ
  yNum : ℤ
  yDen : ℕ

/-- The denominators are positive. -/
def FracPoint.Valid (p : FracPoint) : Prop := 0 < p.xDen ∧ 0 < p.yDen

/-- The point denoted by the fractions. -/
noncomputable def FracPoint.toPoint (p : FracPoint) : Point :=
  ((p.xNum : ℝ) / (p.xDen : ℝ), (p.yNum : ℝ) / (p.yDen : ℝ))

/-- The code of a vertex: the four numbers in binary. -/
def FracPoint.encode (p : FracPoint) : Word :=
  binaryInt p.xNum ++ binaryNat p.xDen ++ binaryInt p.yNum ++ binaryNat p.yDen

/-- The code of an art-gallery instance: the vertex list, then the number of guards in binary. -/
def encodeAGP (V : List FracPoint) (g : ℕ) : Word :=
  encodeList FracPoint.encode V ++ binaryNat g

/-- **The art gallery problem**: the codes of the instances (a simple polygon with rational
vertex coordinates, given in binary, and a number `g`) for which the polygon has a guard set of
cardinality `g`. -/
def AGP : Language := fun w => ∃ (V : List FracPoint) (g : ℕ),
  encodeAGP V g = w ∧ (∀ p ∈ V, p.Valid) ∧
    (Polygon.mk (V.map FracPoint.toPoint)).Simple ∧
    (Polygon.mk (V.map FracPoint.toPoint)).HasGuardSetOfCard g

/-- **The point-boundary art gallery problem**: the codes of the instances (a simple polygon with
rational vertex coordinates, given in binary, and a number `g`) for which the boundary of the
polygon can be guarded by `g` points of the polygon. -/
def AGPPointBoundary : Language := fun w => ∃ (V : List FracPoint) (g : ℕ),
  encodeAGP V g = w ∧ (∀ p ∈ V, p.Valid) ∧
    (Polygon.mk (V.map FracPoint.toPoint)).Simple ∧
    (Polygon.mk (V.map FracPoint.toPoint)).HasBoundaryGuardSetOfCard g

/-- **The boundary-point art gallery problem**: the codes of the instances (a simple polygon with
rational vertex coordinates, given in binary, and a number `g`) for which the polygon can be
guarded by `g` points of its boundary. -/
def AGPBoundaryPoint : Language := fun w => ∃ (V : List FracPoint) (g : ℕ),
  encodeAGP V g = w ∧ (∀ p ∈ V, p.Valid) ∧
    (Polygon.mk (V.map FracPoint.toPoint)).Simple ∧
    (Polygon.mk (V.map FracPoint.toPoint)).HasGuardSetOnBoundaryOfCard g

/-- The code of an instance with integer vertex coordinates. -/
def encodeAGPInt (V : List (ℤ × ℤ)) (g : ℕ) : Word :=
  encodeList (fun p : ℤ × ℤ => binaryInt p.1 ++ binaryInt p.2) V ++ binaryNat g

/-- **The art gallery problem with integer coordinates**: the codes of the instances (a simple
polygon with integer vertex coordinates, given in binary, and a number `g`) for which the
polygon has a guard set of cardinality `g`. -/
def AGPInt : Language := fun w => ∃ (V : List (ℤ × ℤ)) (g : ℕ),
  encodeAGPInt V g = w ∧
    (Polygon.mk (V.map intPoint)).Simple ∧
    (Polygon.mk (V.map intPoint)).HasGuardSetOfCard g

end ArtGallery

/-! ## The advertised theorems -/

namespace ArtGallery

open Complexity

/-- **Theorem 16.** ETR-INV is `∃ℝ`-complete. -/
theorem etrinv_erComplete : ERComplete ETRINV := by
  sorry

/-- **Theorem 13.** The art gallery problem is in `∃ℝ`. -/
theorem agp_inER : InER AGP := by
  sorry

/-- **Improvement on the open problem of §7.2.** The art gallery problem reduces in polynomial time
to ETR by formulas whose only variables are the `2g` coordinates of the `g` guards (the paper's
formula uses `(n + g)^6` variables, `n` the number of corners). -/
theorem agp_inER_guard_variables :
    ∃ f : Word → Word, PolyTime f ∧ (∀ w, AGP w ↔ ETR (f w)) ∧
      ∀ (V : List FracPoint) (g : ℕ), ∃ φ : ETR.Formula,
        f (encodeAGP V g) = φ.encode ∧ φ.VarsLt (2 * g) := by
  sorry

/-- **Theorem 1.** The art gallery problem is `∃ℝ`-complete. -/
theorem agp_erComplete : ERComplete AGP := by
  sorry

/-- **Theorem 1** (restricted variant). The art gallery problem is `∃ℝ`-complete even for
polygons with integer vertex coordinates. -/
theorem agpInt_erComplete : ERComplete AGPInt := by
  sorry

/-- **Stade (SoCG 2025).** The point-boundary art gallery problem (guards anywhere in the polygon,
only the boundary must be seen) is `∃ℝ`-complete. -/
theorem agpPointBoundary_erComplete : ERComplete AGPPointBoundary := by
  sorry

/-- The point-boundary art gallery problem reduces in polynomial time to ETR by formulas whose only
variables are the `2g` coordinates of the `g` guards. -/
theorem agpPointBoundary_inER_guard_variables :
    ∃ f : Word → Word, PolyTime f ∧ (∀ w, AGPPointBoundary w ↔ ETR (f w)) ∧
      ∀ (V : List FracPoint) (g : ℕ), ∃ φ : ETR.Formula,
        f (encodeAGP V g) = φ.encode ∧ φ.VarsLt (2 * g) := by
  sorry

/-- The boundary-point art gallery problem (guards on the boundary, the whole region must be seen)
is `∃ℝ`-complete. -/
theorem agpBoundaryPoint_erComplete : ERComplete AGPBoundaryPoint := by
  sorry

/-- The boundary-point art gallery problem reduces in polynomial time to ETR by formulas whose only
variables are the `2g` coordinates of the `g` guards. -/
theorem agpBoundaryPoint_inER_guard_variables :
    ∃ f : Word → Word, PolyTime f ∧ (∀ w, AGPBoundaryPoint w ↔ ETR (f w)) ∧
      ∀ (V : List FracPoint) (g : ℕ), ∃ φ : ETR.Formula,
        f (encodeAGP V g) = φ.encode ∧ φ.VarsLt (2 * g) := by
  sorry

/-- **Theorem 54.** For every ETR-INV instance `Φ` on the variables `x 0, …, x (n-1)` there is
a simple polygon with rational vertices, a number `g` and rational shifts `d i` such that every
guard set has at least `g` guards, and an assignment `x` solves `Φ` (with every variable in
`[1/2, 2]`) iff every `x i` is in `[1/2, 2]` and some guard set of cardinality `g` contains the
guards `(x i + d i, 0)`; moreover
every guard set of cardinality `g` contains these guards for some solution `x`. -/
theorem etrinv_guard_correspondence (Φ : List ETRINV.Constraint) (n : ℕ)
    (hΦ : ∀ c ∈ Φ, c.VarsLt n) :
    ∃ (V : List (ℚ × ℚ)) (g : ℕ) (d : ℕ → ℚ),
      (Polygon.mk (V.map ratPoint)).Simple ∧
      (∀ G : Finset Point, (Polygon.mk (V.map ratPoint)).IsGuardSet (G : Set Point) →
        g ≤ G.card) ∧
      (∀ G : Finset Point, (Polygon.mk (V.map ratPoint)).IsGuardSet (G : Set Point) →
        G.card = g → ∃ x : ℕ → ℝ, ((∀ i < n, 1 / 2 ≤ x i ∧ x i ≤ 2) ∧ ∀ c ∈ Φ, c.Holds x) ∧
          ∀ i < n, (x i + (d i : ℝ), (0 : ℝ)) ∈ G) ∧
      ∀ x : ℕ → ℝ,
        ((∀ i < n, 1 / 2 ≤ x i ∧ x i ≤ 2) ∧ ∀ c ∈ Φ, c.Holds x) ↔
          (∀ i < n, 1 / 2 ≤ x i ∧ x i ≤ 2) ∧ ∃ G : Finset Point, G.card = g ∧
            (Polygon.mk (V.map ratPoint)).IsGuardSet (G : Set Point) ∧
            ∀ i < n, (x i + (d i : ℝ), (0 : ℝ)) ∈ G := by
  sorry

/-- **Theorem 55.** For every formula `φ` of the existential theory of the reals on the
variables `x 0, …, x (n-1)` there is a simple polygon with rational vertices, a number `g` and
rational constants `c i ≠ 0`, `d i` such that every guard set has at least `g` guards, the
polygon has a guard set of cardinality `g` if `φ` is satisfiable, and every guard set of
cardinality `g` contains the guards `(c i * x i + d i, 0)` for some solution `x` of `φ`. -/
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
  sorry

/-- **Theorem 2.** For every real algebraic number `α` there is a simple polygon with rational
vertex coordinates that has an optimal guard set, and every optimal guard set of it contains a
guard with `x`-coordinate `α`. -/
theorem algebraic_guard_coordinate (α : ℝ) (hα : IsAlgebraic ℚ α) :
    ∃ V : List (ℚ × ℚ),
      (Polygon.mk (V.map ratPoint)).Simple ∧
      (∃ G : Finset Point, (Polygon.mk (V.map ratPoint)).IsOptimalGuardSet G) ∧
      ∀ G : Finset Point, (Polygon.mk (V.map ratPoint)).IsOptimalGuardSet G →
        ∃ p ∈ G, p.1 = α := by
  sorry

/-- **Theorem 4.** There is a simple monotone polygon with integer vertex coordinates that can
be guarded by three guards, while the optimal guard sets with guards at rational points have
four guards. -/
theorem irrational_guards_needed :
    ∃ V : List (ℤ × ℤ),
      (Polygon.mk (V.map intPoint)).Simple ∧
      (Polygon.mk (V.map intPoint)).XMonotone ∧
      (Polygon.mk (V.map intPoint)).HasGuardSetOfCard 3 ∧
      (∃ G : Finset Point, G.card = 4 ∧
        (Polygon.mk (V.map intPoint)).IsGuardSet (G : Set Point) ∧
        ∀ p ∈ G, IsRationalPoint p) ∧
      ∀ G : Finset Point, (Polygon.mk (V.map intPoint)).IsGuardSet (G : Set Point) →
        (∀ p ∈ G, IsRationalPoint p) → 4 ≤ G.card := by
  sorry

end ArtGallery

end
