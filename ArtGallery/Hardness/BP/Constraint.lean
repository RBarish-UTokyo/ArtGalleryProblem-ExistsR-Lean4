module

public import ArtGallery.Hardness.BP.ConstraintGlobal

/-!
# Boundary-point variant: constraints — facts (iv) and (v) with guards on the boundary (umbrella)

A set of guards on the boundary of `polyCBP Φ n` that sees the whole polygon and has
`numGuardsBP Φ n` guards encodes a solution of `Φ` (`Constraint.guardSet_solutionBP`).

* `ConstraintUnit.lean`: the receivers among the boundary-point template positions
  (`recvIdxBP`), the hypotheses `UnitGBP` on the guards seen from one unit, the copy statement
  (`UnitGBP.recv_eq`, from the Section 5 corridor copy lemma), template zones are seen only by
  template positions (`UnitGBP.zone_seen`);
* `ConstraintKinds.lean`: the mechanism of the four boundary-point templates (`ge_mechBP`, …) and
  the relation enforced by a unit of each kind (`UnitGBP.ge_rel`, …);
* `ConstraintGlobal.lean`: the guards of a side (`SideGBP`), from the pinned guards
  (`Count.count_pinnedBP`) to the two sides, **`guardSet_solutionBP`**, and
  **`base_guard_uniqueBP`**.
-/
