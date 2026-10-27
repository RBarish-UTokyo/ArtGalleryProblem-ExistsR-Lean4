module

public import ArtGallery.Hardness.Sec5.CountGlobal

/-!
# Section 5: counting — facts (ii) and (iii) of `08_proof_plan.md` §1 (umbrella)

* `CountAbstract.lean`: positions grouped in zones, two-stage counting (`card_le_of_zones`,
  `pinned_of_zones`), transport of a zone along a visibility-preserving bijection;
* `CountTools.lean`: template position systems (`TSys`, `TSys.Facts`) and certificate tools;
* `CountTmpl{GE,LE,Orient,Inv}.lean`: `TSys.Facts` for the four templates (generated);
* `CountCorridor.lean`: slot witnesses of different corridor stationary guards;
* `CountUnit.lean`: the positions of one unit (`UnitHyp.ok`);
* `CountSide.lean`: the unit room, every unit of a side satisfies `UnitHyp`;
* `CountMain.lean`: the base positions (`MainHyp.ok`);
* `CountGlobal.lean`: the zones of the global polygon, `card_pos`, **`count_lower`** (ii),
  **`count_pinned`** (iii), and the explicit positions `gPosSpot_*`.
-/
