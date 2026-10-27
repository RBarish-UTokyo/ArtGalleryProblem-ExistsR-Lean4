module

public import ArtGallery.Hardness.Sec5.ConstraintGlobal

/-!
# Section 5: constraints — facts (iv) and (v) of `08_proof_plan.md` §1 (umbrella)

A guard set of `polyC Φ n` with `numGuards Φ n` guards encodes a solution of `Φ`
(`Constraint.guardSet_solution`).

* `ConstraintTools.lean`: rooms, foreign points (other units, the other side, base guards) do not
  see critical points (`foreign_not_sees_corr`, `foreign_not_sees_tmpl`), the band lemma for
  template points (`tmpl_band`), seeing a pocket's top edge only past its mouth corners
  (`west_wall`, `east_wall`);
* `ConstraintCopy.lean`: (iv) the corridor copies offsets exactly (`Good.copy_eq`);
* `ConstraintUnit.lean`: the receivers among the template positions, the hypotheses `UnitG` on the
  guards seen from one unit, the copy statement for a unit (`UnitG.recv_eq`), template zones are
  seen only by template positions (`UnitG.zone_seen`);
* `ConstraintTmpl.lean`: (v) the mechanism of the four templates (`ge_mech`, `le_mech`,
  `orient_mech`, `inv_mech`);
* `ConstraintKinds.lean`: the relation enforced by a unit of each kind (`UnitG.ge_rel`, …);
* `ConstraintSide.lean`: the guards of a side (`SideG`) satisfy `UnitG` for every unit;
* `ConstraintGlobal.lean`: from the pinned guards (`Count.count_pinned`) to the two sides, and
  **`guardSet_solution`**.
-/
