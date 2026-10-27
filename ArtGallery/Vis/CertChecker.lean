module

public import ArtGallery.Vis.CertCheckerBasic
public import ArtGallery.Vis.CertCheckerSimple
public import ArtGallery.Vis.CertCheckerTransfer
public import ArtGallery.Vis.CertCheckerCross
public import ArtGallery.Vis.CertCheckerPiece

/-!
# Kernel-checkable certificates for polygons with integer vertices

Verified Boolean checks on integer data, evaluated by `decide +kernel`, with soundness theorems
about the polygon `Polygon.mk (V.map intPoint)` (namespace `ArtGallery.Vis.Cert`):

* `simple_of_simpleCheck : simpleCheck V = true → (Polygon.mk (V.map intPoint)).Simple`
  (`CertCheckerSimple`, `CertCheckerTransfer`; the core works on natural coordinates,
  `simple_of_simpleCheckN`);
* `not_sees_of_crossCheck : P.Simple → crossCheck V i P₁ Q₁ = true →
    ∀ p ∈ convexHull ℝ (intSet P₁), ∀ q ∈ convexHull ℝ (intSet Q₁), ¬ P.Sees p q`
  (`CertCheckerCross`);
* `disjoint_interior_of_pieceCheck : pieceCheck V Q = true →
    ∀ i < P.n, Disjoint (interior (convexHull ℝ (intSet Q))) (P.edge i)` and
  `hull_subset_filled_of_pieceCheck` (`CertCheckerPiece`; half-plane form `pieceCheckHP`);
* cone certificates `convex_corner_of_check`, `inCone_of_check`, `outCone_of_check`
  (`CertCheckerCross`);
* transfer lemmas for similarities, reversal and the mirror `x ↦ c − x` with reversal, and the
  rational forms for data `ratScale D V` (`CertCheckerTransfer`, and the `…ratScale…`
  theorems).

**Usage.**  Put the vertex list in a definition and close the check by `decide +kernel`:
```
def V : List (ℤ × ℤ) := [(0, 0), (4, 0), (4, 4), (0, 4)]
example : (Polygon.mk (V.map intPoint)).Simple := simple_of_simpleCheck (by decide +kernel)
```
Large data lists are best declared `noncomputable def` (the compiler then does not generate code
for them, which otherwise dominates the elaboration time); this does not affect `decide +kernel`.
-/

@[expose] public section

end
