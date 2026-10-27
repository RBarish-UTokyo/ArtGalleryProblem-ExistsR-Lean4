module

public import ArtGallery.Stade.Polygon
public import ArtGallery.Stade.Guarding
public import ArtGallery.Stade.GuardGadgetAPI
public import ArtGallery.Stade.Lower

/-!
# Stade's construction: the three correctness statements (interface)

Proof plan §0 (`docs/stade/proof_plan.md`): for an ETR-INV-REV instance `Φ` on the variables
`< n`, the polygon `poly n Φ` and the number `guards n Φ` satisfy
* (a) every boundary guard set has at least `guards n Φ` guards;
* (b) a solution gives a guard set (of the whole region) of cardinality `guards n Φ` with the
  guard of variable `i` at `(varX i, varY0 + 2 v i)`;
* (c) a boundary guard set of cardinality `guards n Φ` encodes a solution.
This file fixes the statements; the proofs are assembled in `ArtGallery/Stade/Lower.lean` and
`ArtGallery/Stade/Guarding.lean`.
-/

@[expose] public section

namespace ArtGallery.Stade

open ArtGallery.ETRINVREV

/-- (a) Lower bound. -/
theorem card_le_of_boundaryGuard (n : ℕ) (Φ : List Constraint) (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    (G : Finset Point)
    (hG : (Polygon.mk ((poly n Φ).map ratPoint)).IsBoundaryGuardSet (G : Set Point)) :
    guards n Φ ≤ G.card :=
  card_le_of_boundaryGuard' n Φ G hG

/-- (b) A solution gives a guard set of cardinality `guards n Φ` (for `n ≥ 1`: for `n = 0` the
polygon is a rectangle and `guards 0 [] = 0`). -/
theorem guardSet_of_sat (n : ℕ) (Φ : List Constraint) (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n)
    {v : ℕ → ℝ} (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) (hsol : ∀ c ∈ Φ, c.Holds v) :
    ∃ G : Finset Point, G.card = guards n Φ ∧
      (Polygon.mk ((poly n Φ).map ratPoint)).IsGuardSet (G : Set Point) ∧
      ∀ i < n, ((varX n Φ i : ℝ), (varY0 n Φ : ℝ) + 2 * v i) ∈ G :=
  guardSet_of_sat_of_region hn (regionDecomp n Φ hΦ) hv hsol

/-- (c) A boundary guard set of cardinality `guards n Φ` encodes a solution. -/
theorem sat_of_boundaryGuard (n : ℕ) (Φ : List Constraint) (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    (G : Finset Point)
    (hG : (Polygon.mk ((poly n Φ).map ratPoint)).IsBoundaryGuardSet (G : Set Point))
    (hcard : G.card = guards n Φ) :
    ∃ v : ℕ → ℝ, (∀ i < n, 1 / 2 ≤ v i ∧ v i ≤ 2) ∧ (∀ c ∈ Φ, c.Holds v) ∧
      ∀ i < n, ((varX n Φ i : ℝ), (varY0 n Φ : ℝ) + 2 * v i) ∈ G :=
  sat_of_boundaryGuard' n Φ hΦ G hG hcard

end ArtGallery.Stade

end
