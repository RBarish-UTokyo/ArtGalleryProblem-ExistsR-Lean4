module

public import ArtGallery.MainTheorems
public import ArtGallery.Hardness.Correspondence
public import ArtGallery.Irrational.Main
public import ArtGallery.Corollaries.Theorem55
public import ArtGallery.Corollaries.Theorem2
public import ArtGallery.FewVars.Main
public import ArtGallery.FewVars.BoundaryMain
public import ArtGallery.FewVars.BoundaryPointMain
public import ArtGallery.Hardness.BP.Main

/-!
# Solution

Imports the proof development; the advertised theorems of `Challenge.lean` are the declarations
of the same names (namespace `ArtGallery`) proved in the library:

* `etrinv_erComplete` (Theorem 16) — `ArtGallery/PTime/ETRtoINV.lean`
* `agp_inER` (Theorem 13) — `ArtGallery/PTime/AGPinER.lean`
* `agp_inER_guard_variables`, `agpPointBoundary_inER_guard_variables`,
  `agpBoundaryPoint_inER_guard_variables` (the open problem of §7.2: `2g` variables suffice) —
  `ArtGallery/FewVars/Main.lean`, `ArtGallery/FewVars/BoundaryMain.lean`,
  `ArtGallery/FewVars/BoundaryPointMain.lean`
* `agp_erComplete`, `agpInt_erComplete` (Theorem 1) and `agpPointBoundary_erComplete` (Stade, SoCG
  2025) — `ArtGallery/MainTheorems.lean`, through Stade's construction (`ArtGallery/Stade/`)
* `agpBoundaryPoint_erComplete` (the boundary-point variant) — `ArtGallery/MainTheorems.lean`,
  through the boundary-point form of the Section 5 construction (`ArtGallery/Hardness/BP/`)
* `etrinv_guard_correspondence` (Theorem 54) — `ArtGallery/Hardness/Correspondence.lean`, proved
  by the Section 5 construction (`ArtGallery/Hardness/Sec5/`)
* `etr_guard_correspondence` (Theorem 55) — `ArtGallery/Corollaries/Theorem55.lean`
* `algebraic_guard_coordinate` (Theorem 2) — `ArtGallery/Corollaries/Theorem2.lean`
* `irrational_guards_needed` (Theorem 4) — `ArtGallery/Irrational/Main.lean`
-/
