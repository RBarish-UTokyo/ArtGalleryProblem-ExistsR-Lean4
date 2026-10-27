module

public import ArtGallery.Hardness.Sec5.Assemble.Construct
public import ArtGallery.Hardness.Sec5.Assemble.Check
public import ArtGallery.Hardness.Sec5.Assemble.Simple
public import ArtGallery.Hardness.Sec5.Assemble.Sides
public import ArtGallery.Hardness.Sec5.Assemble.Sep

/-!
# Section 5: the global polygon (umbrella)

* `Assemble/Construct.lean`: `construct Φ n`, `numGuards`, `unitChain`, `unitInput`;
* `Assemble/Check.lean`: agreement with reference vertex lists on three instances;
* `Assemble/Simple.lean`: `construct_simple` (simple and counter-clockwise), `construct_global`;
* `Assemble/Sides.lean`: `rightSide`, `leftSide` (`SideAt`): placement of every unit, with
  `SideAt.corridorAt`, `SideAt.corridorClear`, `SideAt.chainAt`, `SideAt.sep_walls`;
* `Assemble/Sep.lean`: bridge to the template data, `SideAt.sepAt`, `SideAt.sepAt_inv`,
  `SideAt.tmpl_simple`, `SideAt.tmpl_ccw`.
-/
