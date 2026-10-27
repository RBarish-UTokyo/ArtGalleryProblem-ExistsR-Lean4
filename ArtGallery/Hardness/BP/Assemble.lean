module

public import ArtGallery.Hardness.BP.Assemble.TmplData
public import ArtGallery.Hardness.BP.Assemble.Construct
public import ArtGallery.Hardness.BP.Assemble.Check
public import ArtGallery.Hardness.BP.Assemble.TmplFacts
public import ArtGallery.Hardness.BP.Assemble.UnitChain
public import ArtGallery.Hardness.BP.Assemble.Global
public import ArtGallery.Hardness.BP.Assemble.Simple
public import ArtGallery.Hardness.BP.Assemble.Side
public import ArtGallery.Hardness.BP.Assemble.Sides
public import ArtGallery.Hardness.BP.Assemble.Sep
public import ArtGallery.Hardness.BP.Assemble.Bays
public import ArtGallery.Hardness.BP.Assemble.MainGlobal
public import ArtGallery.Hardness.BP.Assemble.PTime

/-!
# Boundary-point variant: the assembly of the global polygon

* `Assemble/TmplData`, `Assemble/Construct`: the template data of the boundary-point templates and
  the polygon `constructBP Φ n` (bottom wall with bays, units with the new templates, mirrored left
  units), `numGuardsBP`; `Assemble/Check`: kernel-checked agreement with
  reference vertex lists on three instances.
* `Assemble/TmplFacts`, `Assemble/UnitChain`, `Assemble/Global`, `Assemble/Simple`:
  `constructBP_simple` (simple and counter-clockwise) and `constructBP_global`.
* `Assemble/Side`, `Assemble/Sides`, `Assemble/Sep`: every unit sits in the global polygon
  (`rightSideBP`, `leftSideBP`): `CorridorAt`, `CorridorClear`, `Good`, the template chain
  (`Tmpl.ChainAt`) and its separation (`Tmpl.SepAt`, region of `BP/Templates/*Data.lean`).
* `Assemble/Bays`: every receiver bay of every unit is a separated bay (`BayAt`, `BaySep`), in
  template coordinates and in the polygon itself.
* `Assemble/MainGlobal`: the main area — `pocketsBP`, `boxSepBP`, `mainHypBP`, `hexHypBP`.
* `Assemble/PTime`: `PT.constructBP`, `PT.numGuardsBP`, `PT.constructInstanceBP`.
-/
