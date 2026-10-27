module

public import ArtGallery.Spec
public import ArtGallery.Stade.Main
public import ArtGallery.Hardness.BP.Main

/-!
# Polynomial-time reductions from ETR to the art gallery problems (interface)

Hardness is proved through Stade's construction (SoCG 2025): ETR → ETR-INV-REV
(`ArtGallery/ETR/REV.lean`) → the polygon `ArtGallery.Stade.poly`, scaled to integer
coordinates.  The same polygon works for the point-point and the point-boundary problem.
The boundary-point problem goes through ETR-INV (`ArtGallery/ETR/Reduction.lean`) and the
boundary-point variant of the Section 5 construction (`ArtGallery/Hardness/BP/`).
This file fixes the statements; the proofs are in `ArtGallery/Stade/Main.lean` and
`ArtGallery/Hardness/BP/Main.lean`.
-/

@[expose] public section

namespace ArtGallery

open Complexity

/-- ETR reduces in polynomial time to the art gallery problem with integer coordinates. -/
theorem etr_polyRed_agpInt : PolyRed ETR AGPInt :=
  Stade.etr_polyRed_agpInt'

/-- ETR reduces in polynomial time to the point-boundary art gallery problem. -/
theorem etr_polyRed_agpPointBoundary : PolyRed ETR AGPPointBoundary :=
  Stade.etr_polyRed_agpPointBoundary'

/-- ETR reduces in polynomial time to the boundary-point art gallery problem. -/
theorem etr_polyRed_agpBoundaryPoint : PolyRed ETR AGPBoundaryPoint :=
  BP.etr_polyRed_agpBoundaryPoint'

end ArtGallery

end
