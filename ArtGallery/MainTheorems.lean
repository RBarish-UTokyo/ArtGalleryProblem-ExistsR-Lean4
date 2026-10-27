module

public import ArtGallery.Hardness.ReductionAPI
public import ArtGallery.PTime.AGPinER
public import ArtGallery.PTime.ETRtoINV
public import ArtGallery.FewVars.BoundaryMain
public import ArtGallery.FewVars.BoundaryPointMain

/-!
# Theorem 1: the art gallery problem is ∃ℝ-complete

Membership (Theorem 13, `ArtGallery.PTime.AGPinER`), hardness via Stade's construction
(`ArtGallery.Hardness.ReductionAPI`, `ArtGallery/Stade/`); the point-boundary variant (Stade) and
the boundary-point variant (hardness via the boundary-point form of the Section 5 construction,
`ArtGallery/Hardness/BP/`).
-/

@[expose] public section

namespace ArtGallery

open Complexity

/-- **Theorem 1** (restricted variant). The art gallery problem is `∃ℝ`-complete even for
polygons with integer vertex coordinates. -/
theorem agpInt_erComplete : ERComplete AGPInt :=
  ERComplete.of_polyRed_ETR agpInt_inER etr_polyRed_agpInt

/-- **Theorem 1.** The art gallery problem is `∃ℝ`-complete. -/
theorem agp_erComplete : ERComplete AGP :=
  ERComplete.of_polyRed agp_inER agpInt_erComplete.2 agpInt_polyRed_agp

/-- **Stade (SoCG 2025).** The point-boundary art gallery problem is `∃ℝ`-complete. -/
theorem agpPointBoundary_erComplete : ERComplete AGPPointBoundary :=
  ERComplete.of_polyRed_ETR agpPointBoundary_inER etr_polyRed_agpPointBoundary

/-- The boundary-point art gallery problem (guards on the boundary, the whole region must be seen)
is `∃ℝ`-complete. -/
theorem agpBoundaryPoint_erComplete : ERComplete AGPBoundaryPoint :=
  ERComplete.of_polyRed_ETR agpBoundaryPoint_inER etr_polyRed_agpBoundaryPoint

end ArtGallery

end
