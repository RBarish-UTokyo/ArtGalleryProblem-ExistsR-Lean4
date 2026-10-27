module

public import ArtGallery.Hardness.BP.CountGlobal

/-!
# Boundary-point variant: counting — facts (ii) and (iii) with guards on the boundary (umbrella)

* `MainAreaCount.lean`: the base positions (`MainHypBP.okOn`);
* `CountUnit.lean`: the positions of one unit (`UnitHypBP.okOn`, `UnitHypBP.spot_bd`);
* `CountSide.lean`: the template positions of a kind (`tsysOfBP`, `tsysOfBP_facts`), every unit
  of a side satisfies `UnitHypBP` (`side_unitHypBP`);
* `CountGlobal.lean`: the zones of the global polygon, `card_posBP`, **`count_lowerBP`** (ii),
  **`count_pinnedBP`** (iii), the explicit positions `gPosSpotBP_*`, their disjointness
  (`gPosSpotBP_disjoint`) and `gPosSpotBP_subset_boundary`.
-/
