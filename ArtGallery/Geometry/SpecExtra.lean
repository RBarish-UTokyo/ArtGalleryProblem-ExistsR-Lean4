module

public import ArtGallery.Spec
public import Mathlib.Analysis.Convex.Hull

/-!
# Geometric definitions beyond the specification

The orientation determinant and triangulations, as in the specification of the Palomar entry
PALOMAR-2026-10-05-000003, `LinearTimeTriangulation-ChazelleAlgorithm-Lean4`
(`Chazelle/Spec.lean`), whose geometric
library (`ArtGallery/Geometry`, `ArtGallery/Jordan`, `ArtGallery/Existence`) is reused here
with the namespace renamed.
-/

@[expose] public section

namespace ArtGallery

/-- Twice the signed area of the triangle `a b c`; nonzero exactly when the
three points are not collinear. -/
def det (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2)

namespace Polygon

variable (P : Polygon)

/-- A triangle is named by three vertex indices. -/
abbrev Triangle : Type := ℕ × ℕ × ℕ

/-- The three vertex points of a triangle. -/
def triVertices (t : Triangle) : Set Point := {P.vtx t.1, P.vtx t.2.1, P.vtx t.2.2}

/-- The closed triangle: the convex hull of its three vertices. -/
def triSet (t : Triangle) : Set Point := convexHull ℝ (P.triVertices t)

/-- A triangle is valid when its indices are in range and its vertices are not
collinear. -/
def validTriangle (t : Triangle) : Prop :=
  t.1 < P.n ∧ t.2.1 < P.n ∧ t.2.2 < P.n ∧ det (P.vtx t.1) (P.vtx t.2.1) (P.vtx t.2.2) ≠ 0

/-- `T` triangulates `P`: exactly `n − 2` valid triangles on the vertices of `P`
that cover exactly the filled region, have pairwise disjoint interiors, and are
conforming. -/
def Triangulates (T : List Triangle) : Prop :=
  (∀ t ∈ T, P.validTriangle t) ∧
  T.length + 2 = P.n ∧
  {p | ∃ t ∈ T, p ∈ P.triSet t} = P.filled ∧
  T.Pairwise (fun s t => Disjoint (interior (P.triSet s)) (interior (P.triSet t))) ∧
  T.Pairwise (fun s t =>
    P.triSet s ∩ P.triSet t = convexHull ℝ (P.triVertices s ∩ P.triVertices t))

end Polygon

end ArtGallery

end
