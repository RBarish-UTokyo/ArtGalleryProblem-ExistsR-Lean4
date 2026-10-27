module

public import ArtGallery.Corollaries.Theorem2Stade

/-!
# Theorem 2: every real algebraic number is a guard coordinate of an optimal guard set

The proof goes through Stade's construction (`ArtGallery/Corollaries/Theorem2Stade.lean`,
`algebraic_guard_coordinate'`): root isolation gives an ETR formula whose unique solution is
`α`; its ETR-INV-REV instance yields Stade's polygon, in which every optimal guard set contains
a guard whose `y`-coordinate is a rational affine image of `α`; a rational affine map swapping
the coordinates moves it to `x`-coordinate `α`.  Theorem 54 is not used.
-/

@[expose] public section

namespace ArtGallery

/-- **Theorem 2.** For every real algebraic number `α` there is a simple polygon with rational
vertex coordinates that has an optimal guard set, and every optimal guard set of it contains a
guard with `x`-coordinate `α`. -/
theorem algebraic_guard_coordinate (α : ℝ) (hα : IsAlgebraic ℚ α) :
    ∃ V : List (ℚ × ℚ),
      (Polygon.mk (V.map ratPoint)).Simple ∧
      (∃ G : Finset Point, (Polygon.mk (V.map ratPoint)).IsOptimalGuardSet G) ∧
      ∀ G : Finset Point, (Polygon.mk (V.map ratPoint)).IsOptimalGuardSet G →
        ∃ p ∈ G, p.1 = α :=
  algebraic_guard_coordinate' α hα

end ArtGallery

end
