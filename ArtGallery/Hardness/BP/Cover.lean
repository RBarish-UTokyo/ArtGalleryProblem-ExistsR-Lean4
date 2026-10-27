module

public import ArtGallery.Hardness.BP.CoverMain

/-!
# Boundary-point variant: coverage by the canonical guards

For `∀ c ∈ Φ, c.VarsLt n`, `0 < n` and an assignment `x` with values in `[1/2, 2]` satisfying `Φ`,
the canonical guard set `canonGuardsBP Φ n x` (`docs/boundary_point/design.md` §3.4) of the global
polygon `polyCBP Φ n`:

* lies on the boundary (`canonGuardsBP_boundary`);
* has `numGuardsBP Φ n` points (`canonGuardsBP_card`);
* contains the base guards `(x_i + d_i, 0)` (`canonGuardsBP_mem`);
* sees every point of the region (`canonGuardsBP_sees`); together: `canonGuardsBP_guard`
  (`IsGuardSetOnBoundary`).

Files (the Section 5 coverage, `Sec5/Cover*.lean`, adapted to bays and the boundary-point
templates):

* `CoverChanData`: the channel certificates of the four boundary-point templates;
* `CoverKind`: the template facts by kind and the canonical template guards (T-cover);
* `CoverUnit`, `CoverUnitLocal`: the pieces of a unit (corridor, channel, template room), their
  coverage and the room property of the unit region;
* `CoverSide`, `CoverGlob`, `CoverRegion`: the region of the global polygon is the union of the
  hexagon, the pocket rooms with bays and the unit regions;
* `CoverCanon`: the canonical points of the positions (`Count.GPosBP`), cardinality and boundary;
* `CoverMain`: the coverage of the pieces by the canonical guards.
-/
