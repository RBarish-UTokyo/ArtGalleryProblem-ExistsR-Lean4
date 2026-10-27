module

public import Complexity.Classes
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Finset.Card
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.RingTheory.Algebraic.Defs

/-!
# Specification: the art gallery problem is ∃ℝ-complete

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

@[expose] public section

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

end
