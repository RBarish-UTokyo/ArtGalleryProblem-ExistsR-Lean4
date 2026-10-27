module

public import ArtGallery.Geometry.SpecExtra
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import ArtGallery.Vis.Orientation
public import ArtGallery.Vis.Blocking
public import ArtGallery.Vis.Guards

/-!
# Visibility library: interface

General facts about simple polygons used throughout the development (membership, Section 2,
Section 5).  This file fixes the statements; the proofs live in `ArtGallery/Vis/`.

Notation: for a polygon `P`, edge `i` runs from `P.vtx i` to `P.vtx ((i+1) % P.n)`;
`det a b c` (twice the signed area) is positive iff `c` is strictly to the left of the directed
line `a → b`.
-/

@[expose] public section

namespace ArtGallery

namespace Polygon

variable {P : Polygon}

/-- The left normal of the directed segment `u → v`. -/
def leftNormal (u v : Point) : Point := (-(v.2 - u.2), v.1 - u.1)

/-- The interior is to the left of every edge: for every edge and every point `y` of the open
edge, the points `y + δ·leftNormal` (small `δ > 0`) are interior points (in the region, off the
boundary) and the points `y − δ·leftNormal` are outside the region. -/
def InteriorLeft (P : Polygon) : Prop :=
  ∀ i < P.n, ∀ t : ℝ, 0 < t → t < 1 → ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    (P.vtx i + t • (P.vtx ((i + 1) % P.n) - P.vtx i) +
        δ • leftNormal (P.vtx i) (P.vtx ((i + 1) % P.n))) ∈ P.filled \ P.boundary ∧
    (P.vtx i + t • (P.vtx ((i + 1) % P.n) - P.vtx i) -
        δ • leftNormal (P.vtx i) (P.vtx ((i + 1) % P.n))) ∉ P.filled

/-! ## Orientation -/

/-- A simple polygon whose vertices all have ordinate `≥ y₀`, with an edge on the line
`y = y₀` traversed from left to right, has its interior to the left of every edge. -/
theorem interiorLeft_of_bottom_edge (hP : P.Simple) {i : ℕ} (hi : i < P.n) {y₀ : ℝ}
    (hlow : ∀ j < P.n, y₀ ≤ (P.vtx j).2) (hu : (P.vtx i).2 = y₀)
    (hv : (P.vtx ((i + 1) % P.n)).2 = y₀) (hdir : (P.vtx i).1 < (P.vtx ((i + 1) % P.n)).1) :
    P.InteriorLeft := by
  exact Vis.leftInterior_of_bottom_edge hP hi hlow hu hv hdir

/-! ## Blocking and containment -/

/-- **Blocking (T1).** A segment that properly crosses an edge (the endpoints of each segment
strictly on opposite sides of the line of the other) is not contained in the region. -/
theorem not_sees_of_proper_cross (hP : P.Simple) {i : ℕ} (hi : i < P.n) {p q : Point}
    (h₁ : det (P.vtx i) (P.vtx ((i + 1) % P.n)) p * det (P.vtx i) (P.vtx ((i + 1) % P.n)) q < 0)
    (h₂ : det p q (P.vtx i) * det p q (P.vtx ((i + 1) % P.n)) < 0) :
    ¬ P.Sees p q := by
  exact Vis.not_sees_of_proper_cross hP hi h₁ h₂

/-- **Convex containment (T2).** A convex set whose interior meets no edge and contains a point
of the region lies, with its closure, in the region. -/
theorem closure_subset_filled_of_convex (hP : P.Simple) {Q : Set Point} (hQ : Convex ℝ Q)
    (hedge : ∀ i < P.n, Disjoint (interior Q) (P.edge i)) {z : Point} (hz : z ∈ interior Q)
    (hzP : z ∈ P.filled) : closure Q ⊆ P.filled := by
  exact Vis.closure_subset_filled_of_convex P hQ hedge hz hzP

/-- **Exact region.** A closed set `U ⊆ P.filled` containing the boundary, whose frontier lies in
the boundary and which contains a point off the boundary, is the whole region. -/
theorem filled_eq_of_frontier_subset (hP : P.Simple) {U : Set Point} (hUc : IsClosed U)
    (hbd : P.boundary ⊆ U) (hfr : frontier U ⊆ P.boundary) (hU : U ⊆ P.filled)
    (hne : (U \ P.boundary).Nonempty) : P.filled = U := by
  exact Vis.filled_eq_of_frontier_subset hP hUc hbd hfr hU hne

/-- The region is closed. -/
theorem isClosed_filled (P : Polygon) : IsClosed P.filled := by
  exact Jordan.isClosed_filled P

/-- The boundary lies in the region. -/
theorem boundary_subset_filled (P : Polygon) : P.boundary ⊆ P.filled := fun _ h => Or.inl h

/-- A simple polygon has interior points, and every point of the region is a limit of interior
points. -/
theorem filled_subset_closure_interior (hP : P.Simple) :
    P.filled ⊆ closure (P.filled \ P.boundary) := by
  exact Existence.filled_subset_closure_interior hP

/-! ## Local structure at boundary points (assuming the interior is to the left) -/

/-- Near a point `y` of the open edge `i`, the region is the closed half-plane to the left of the
edge. -/
theorem local_halfplane (hP : P.Simple) (hL : P.InteriorLeft) {i : ℕ} (hi : i < P.n) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ r > 0, ∀ z : Point,
      dist z (P.vtx i + t • (P.vtx ((i + 1) % P.n) - P.vtx i)) < r →
        (z ∈ P.filled ↔ 0 ≤ det (P.vtx i) (P.vtx ((i + 1) % P.n)) z) := by
  exact Vis.local_halfplane hP hL hi ht0 ht1

/-- Near vertex `i` (with predecessor `u` and successor `w`), the region is the closed wedge
to the left of both edges at a convex corner (`det u v w > 0`), the closed union of the two
half-planes at a reflex corner (`det u v w < 0`), and the closed half-plane at a straight
corner. -/
theorem local_wedge (hP : P.Simple) (hL : P.InteriorLeft) {i : ℕ} (hi : i < P.n) :
    ∃ r > 0, ∀ z : Point, dist z (P.vtx i) < r →
      (z ∈ P.filled ↔
        (let u := P.vtx ((i + P.n - 1) % P.n)
         let v := P.vtx i
         let w := P.vtx ((i + 1) % P.n)
         if 0 < det u v w then 0 ≤ det u v z ∧ 0 ≤ det v w z
         else if det u v w < 0 then 0 ≤ det u v z ∨ 0 ≤ det v w z
         else 0 ≤ det u v z)) := by
  exact Vis.local_wedge hP hL hi

/-! ## Guard sets -/

/-- Seeing is symmetric. -/
theorem sees_comm {p q : Point} : P.Sees p q ↔ P.Sees q p := by
  exact Vis.sees_comm

/-- A simple polygon with `n` vertices has a guard set of cardinality `n − 2` (one corner of each
triangle of a triangulation). -/
theorem hasGuardSetOfCard_n_sub_two (hP : P.Simple) : P.HasGuardSetOfCard (P.n - 2) := by
  exact Vis.hasGuardSetOfCard_n_sub_two hP

/-- Padding: a simple polygon with a guard set of cardinality `k` has one of every larger
cardinality (the region is infinite). -/
theorem HasGuardSetOfCard.mono (hP : P.Simple) {k k' : ℕ} (h : P.HasGuardSetOfCard k)
    (hk : k ≤ k') : P.HasGuardSetOfCard k' := by
  exact Vis.HasGuardSetOfCard.mono hP h hk

/-- **Lemma 22/23 of the paper (counting).** Let `A` be a part of the region and `M` a finite set
of points of `A` that are seen only from `A`, no two of them from a common point. Let `W` be a
nonempty set of points seen only from `A`, such that no point sees a point of `M` and a point of
`W`, and every point seeing all of `W` lies in `Spot`. Then every guard set has at least
`|M| + 1` guards in `A`, and if it has exactly `|M| + 1` guards in `A`, one of them lies in
`Spot`. -/
theorem guards_in_region (G : Finset Point) (hG : P.IsGuardSet (G : Set Point))
    (A : Set Point) [DecidablePred (· ∈ A)] (M : Finset Point) (W : Set Point) (Spot : Set Point)
    (hMA : ∀ m ∈ M, m ∈ P.filled) (hMonly : ∀ m ∈ M, ∀ p ∈ P.filled, P.Sees p m → p ∈ A)
    (hMdisj : ∀ m ∈ M, ∀ m' ∈ M, m ≠ m' → ∀ p, P.Sees p m → ¬ P.Sees p m')
    (hWne : W.Nonempty) (hWP : W ⊆ P.filled) (hWonly : ∀ w ∈ W, ∀ p ∈ P.filled, P.Sees p w → p ∈ A)
    (hMW : ∀ m ∈ M, ∀ w ∈ W, ∀ p, P.Sees p m → ¬ P.Sees p w)
    (hSpot : ∀ p ∈ P.filled, (∀ w ∈ W, P.Sees p w) → p ∈ Spot) :
    M.card + 1 ≤ (G.filter (· ∈ A)).card ∧
      ((G.filter (· ∈ A)).card = M.card + 1 → ∃ g ∈ G, g ∈ A ∧ g ∈ Spot) := by
  exact Vis.guards_in_region G hG A M W Spot hMA hMonly hMdisj hWne hWP hWonly hMW hSpot

end Polygon

end ArtGallery

end
