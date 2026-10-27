module

public import ArtGallery.Stade.GuardRegion
public import ArtGallery.Stade.Region

/-!
# Interface for fact (b): the region decomposition (proof plan L2.3)

The proof of fact (b) (`guardSet_of_sat_of_region`, `ArtGallery/Stade/Guarding.lean`) needs
the region of Stade's polygon as the union of the explicit convex pieces `regionPieces n Φ`
(`ArtGallery/Stade/GuardRegion.lean`): the hall `[x_L, x_R] × [−1, 2H]`, the ceiling features
(wedge triangles, copy pockets), the floor needles of the variables, and the pieces of every
gadget slot (`slotPieces`: corridors and pockets of the inversion gadgets, the `invRevLe`
needle hanging from its pocket, the rooms, bay, pockets, aux wedges and room-hung needles of the
addition gadgets, the floor needles of the inputs).

The two inclusions are the statement L2.3 of the proof plan; they are proved in
`ArtGallery/Stade/Region.lean` (`filled_subset_regionPieces'`, `regionPieces_subset_filled'`):
each piece lies in the region by L1.7, and the region lies in their union by the frontier
criterion.  The positive direction of the gadget
lemmas (copy nooks, inversion and addition gadgets) is fully proved (`GuardCopy.lean`,
`GuardInv.lean`, `GuardAdd.lean`, `GuardAddGe.lean`, using `AdditionGeom*.lean`).
-/

@[expose] public section

namespace ArtGallery.Stade

open ArtGallery.ETRINVREV

/-- **L2.3 (⊆).** Every point of the region of `SP n Φ` lies in one of the pieces
`regionPieces n Φ`. -/
theorem filled_subset_regionPieces (n : ℕ) (Φ : List Constraint) (_hΦ : ∀ c ∈ Φ, c.VarsLt n) :
    (SP n Φ).filled ⊆ ⋃ K ∈ regionPieces n Φ, piece K :=
  filled_subset_regionPieces' n Φ

/-- **L2.3 (⊇).** Every piece of `regionPieces n Φ` lies in the region of `SP n Φ`. -/
theorem regionPieces_subset_filled (n : ℕ) (Φ : List Constraint) (_hΦ : ∀ c ∈ Φ, c.VarsLt n) :
    ∀ K ∈ regionPieces n Φ, piece K ⊆ (SP n Φ).filled :=
  regionPieces_subset_filled' n Φ

/-- The region decomposition of Stade's polygon. -/
theorem regionDecomp (n : ℕ) (Φ : List Constraint) (hΦ : ∀ c ∈ Φ, c.VarsLt n) :
    RegionDecomp n Φ :=
  ⟨filled_subset_regionPieces n Φ hΦ, regionPieces_subset_filled n Φ hΦ⟩

end ArtGallery.Stade

end
