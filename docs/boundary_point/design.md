# Boundary-point art gallery problem: ∃ℝ-hardness design

Status: formalized (2026-10-27): `agpBoundaryPoint_erComplete` and
`agpBoundaryPoint_inER_guard_variables` are proved (section 5).

Target statement (`ArtGallery/Spec.lean`): `AGPBoundaryPoint` — guards restricted to the
boundary (`IsGuardSetOnBoundary G`: `G ⊆ P.boundary` and every point of `P.filled` is seen).
Membership is formalized in `FewVars/BoundaryPointMain.lean` (`agpBoundaryPoint_inER`); this
document is about hardness.

---

## 1. Result in one paragraph

The construction is the Section 5 construction of Abrahamsen–Adamaszek–Miltzow (AAM), as
formalized in `ArtGallery/Hardness/Sec5/`, with three local changes: (i) every guard segment
(the `4n` base segments and all template segments) is moved onto a horizontal **boundary edge**,
the floor of a shallow *bay* whose two side walls carry one pinning spike each; (ii) the three
addition-type templates are **re-laid out** (a role swap of their receivers), because in AAM's
layout one receiver is enclosed by sight lines of another and cannot lie on the boundary;
(iii) the inversion template keeps its mechanism and only gets bays.  Corridors, main area,
parameters, unit order, guard number `g` and the shifts `d_i` are unchanged.  The canonical
guards of a solution lie on the boundary and guard the whole polygon; with guards restricted to
the boundary, the spikes pin every guard to its segment (or point) and give the lower bound `g`.
Stade's construction and AAM's own layout fail for topological reasons (section 2).

---

## 2. Why not the other routes

### 2.1 Two facts about boundary guards

**(F1) Half-plane.** A guard in the relative interior of a boundary edge `e` sees only points
of the closed half-plane on the interior side of `e`.  Any witness, nook or critical region that
a guard segment must see on *both* sides of its supporting line is impossible once the segment
lies on an edge.

**(F2) Outer face.** Let `X` be the union of the sight segments that must lie in `P.filled` for
the canonical guards (all sight lines used by coverage and by the copy / addition mechanisms,
over an open set of admissible values, so that they can be taken in the interior of `P`),
together with the regions that must be interior.  The interior of a simple polygon is simply
connected, so the inside of a closed curve in `int P` lies in `int P`.  Hence a guard segment
enclosed by a cycle of `X` lies in `int P` and not on `∂P`: layouts must put every guard
segment on the outer face of the arrangement of its gadget's mandatory sight lines.

### 2.2 Stade's construction (`ArtGallery/Stade/`)

In Stade's problem guards may lie anywhere in `P` and only `∂P` must be seen; for
boundary-point both sides of the requirement flip.  Three independent obstructions:

1. **Two-sided pinning (F1).** Stade pins a variable guard with witnesses on both sides of its
   segment (the copy nooks of the `GE` bundle above, of the `LE` bundle below).  On an edge one
   side is exterior.
2. **No neck (F2).** A variable segment of Stade is enclosed by its own copy bundles: the `GE`
   lines leave above and the `LE` lines below with different slopes, and the region between
   them must be interior to carry the lines.  There is no way to reach the segment from the
   exterior.
3. **Two-dimensional auxiliary guard.** In Stade's addition gadget the position of the
   auxiliary guard determines the pair of summand values `(v_x, v_y)`: it is an injective
   continuous function of the pair, which ranges over a 2-dimensional set of admissible values.
   By invariance of domain its image is not contained in the 1-dimensional `∂P`.  Replacing it
   by a guard with 1-dimensional freedom changes the gadget completely.

Repairing these means a new addition gadget, new copy gadgets with one-sided nooks and a new
variable layout — essentially a new construction, with only the generic tools (`Stade/Exit`,
`Generic/*`, `Counting`, `Chains`, `RobustCheck`, PTime tools) reusable.

### 2.3 AAM's construction as is (paper §7.2)

AAM remark that their construction "can easily be adjusted" to boundary guards.  For base
segments this is true (bays, section 3.1), and corridors need no change.  For the addition templates it is not,
as laid out:

* in the addition template the three receivers `r_i`, `r_j`, `r_l` sit on the strips of the
  corridor, and `r'_i` (weak copy of `r_i`, the τ-max receiver) sits on the far side of the
  mechanism; the copy nook `Q` of `r_i → r'_i` is an arm reaching over the mechanism;
* the middle receiver `r_j` is enclosed by the cycle formed by `r_i`'s strip (below-left,
  which must be interior because `r_i` receives through it), the sight lines `r_i → Q` (above),
  the nook arm `Q` and the sight lines `Q → r'_i` (right), closed by the mechanism lines
  `r'_i → e_i`: a theta graph with `r_j` in a bounded face.  By (F2) `r_j` cannot lie on `∂P`.

### 2.4 Copy direction with same-side guards

Two guard segments on floors (interior above), `W` left of `A`, and a nook above both (the
Section 5 nook construction with corners `k0`, `k1`): the nook region between the two
projections is covered iff `u_A ≤ u_W`.  A nook only enforces one inequality, and with both
segments facing the same side the direction is the one given by the order of the segments and
of the nook corners; in all variants examined, enforcing the opposite inequality required a
guard on the far side of the nook axis, which (F1) excludes.  AAM only use *weak* copies, so this
is no obstruction, but it constrains the role assignment: the weakly copied receiver must be a
summand (the mechanism needs only an upper bound for `A`).

### 2.5 Summary of rejected routes

| route | obstruction |
|---|---|
| Stade, modified | (F1) pinning, (F2) no neck, 2-D auxiliary guard |
| AAM unchanged (paper §7.2) | (F2) theta enclosure of `r_j` in Add templates |
| AAM layout, `r_j` replaced by a copy placed between two jambs on the boundary | (2.4) the link to the original `r_j` needs the inequality direction a same-side nook does not give |
| **AAM with bays + role swap (chosen)** | none; formalized |

---

## 3. The construction

Notation as in `docs/section5/`: `S = C N²` (`C = 200000`, `N = max(4n + k, 2)`), slots
`σ = 0 … 4n−1` with `a_σ = (27σ/2, 0)`, right-oriented base segments for `σ < 3n` (value `1/2`
at the left end, guard `a_σ + (x − 1/2, 0)`), left-oriented for `σ ≥ 3n` (guard
`a_σ + (2 − x, 0)`).  Units (corridor + template) in the order of the Section 5
construction (`unitSpecs`): per variable three `orient` units right and left, per
`add` constraint a `ge` unit (right) and an `le` unit (left), per `inv` constraint an `inv`
unit (right).  Template point `T` ↦ `m + T/S` (`m` = corridor mouth), left units mirrored by
`x ↦ 54n − 12 − x`.

### 3.1 Bays

A bay of a segment `[x0, x0 + 3/2] × {y0}` replaces the pocket (base segments: AAM's 6-unit-deep
pocket; template segments: compact/tilted pockets).  Parameters: floor margin `f = 1/2`, wall
height `d = 1/16`.  Relative vertices (`x0 = y0 = 0`), boundary order, interior above:

```
plain bay:
(-1, 1/8)  (-1/2, 1/16)                                     left shoulder, left rim
(-1/2, 1/64)  (-5/6, 7/384)  (-1/2, 1/128)                  spike w1 (tip (-5/6, 7/384))
(-1/2, 0)  (2, 0)                                           floor (contains the segment [0, 3/2])
(2, 1/128)  (7/3, 7/384)  (2, 1/64)                         spike w2 (tip (7/3, 7/384))
(2, 1/16)  (5/2, 1/8)                                       right rim, right shoulder

bay with a `one` constraint (base slot σ < n): additionally, above w1 / w2,
(-1/2, 3/64) (-4/7, 45/896) (-1/2, 5/128)                   spike o1
(2, 5/128) (33/16, 25/512) (2, 3/64)                        spike o2
```

Cones (the two rays through the mouth corners of a spike, cut off by the floor line):

| spike | rays hit the floor at | role |
|---|---|---|
| `w1` | `x = −1/4` and `x = 3/2` | private witness |
| `w2` | `x = 0` and `x = 7/4` | `w1 ∩ w2` on `∂P` = the segment |
| `o1` | `x = −1/4` and `x = 1/2` | |
| `o2` | `x = 1/2` and `x = 7/4` | `o1 ∩ o2` on `∂P` = the point of value 1 |

Every ray of a spike cone leaves the bay through the floor edge, so the part of `∂P` a spike tip
sees is a piece of the floor (plus the two mouth edges of the spike itself).  In 2-D the two
cones of a bay overlap in a triangle above the segment — the pinning works **only** because
guards are on `∂P` (this is the reason why point-guard pinning statements cannot be reused
verbatim, section 5).  The shoulders rise with slope `d/f` so that every point above them is
seen over the rims; the walls are low (`1/16`) so that a guard on the floor sees the same
upper half-plane as AAM's guard at the mouth of its pocket, up to near-horizontal directions.

Base bays: `bottom_wall` = per slot `a_σ + (−6, 1)` (AAM's pocket mouth corner, unchanged)
followed by the bay chain.  Guard positions `(x_i + d_i, 0)` and `d_i = 27i/2 − 1/2` are
unchanged.

### 3.2 Addition-type templates `AddBP`

Mechanism (AAM Lemma 41, unchanged): corners `e_j = (−v, h)`, `e_l = (0, h)`, `e_i = (v, h)`
with `v = 15`, `h = 21/2`; for guards `A`, `B` on `y = 0` and `C` on `y = −h`, the lines `A e_i`
and `B e_j` meet in `γ`, and the projection of `γ` through `e_l` onto `y = −h` has abscissa
`A.x + B.x` (for every `v`).  The region next to `γ` is seen by `C` iff `C.x ≤ A.x + B.x`, i.e.
`u_C + K ≤ u_A + u_B` with `K = c0 − A0 − B0 + 1/2` (`c0`, `A0`, `B0` the left endpoints).

**Role swap.**  `B` = direct summand = receiver of the *leftmost* strip (τ = 2; it lies on the
lower channel wall, outside every cycle of sight lines); `W` = receiver of the middle strip
(τ = 1), weakly copied by a nook `Q` at the top to `A` (`u_A ≤ u_W`); `C` = sum receiver
(τ = 0).  For `orient` (`u_A + u_B ≥ 5/2`) `C` is replaced by the stationary guard `p` at the
position of value `5/2`, `W` takes τ = 0, `B` τ = 1.  With `u_A ≤ u_W`, "γ-region seen" gives
`u_C + K ≤ u_W + u_B`, the relation of the unit.  Corridor strips: receiver τ on
`x + y = σ0 − 27τ/2` (as in Section 5).

Template coordinates (all segments right-oriented, left endpoints; `A` gets the offset of `W`):

| | `ge` (`u_W + u_B ≥ u_C`, K = 0) | `le` (working frame, `u_W + u_B ≥ u_C + 5/2`) | `orient` (`u_W + u_B ≥ 5/2`) |
|---|---|---|---|
| `C` (τ0) | `(−2, −21/2)` | `(1/2, −21/2)` | `p = (0, −21/2)` (stationary) |
| `W` | `(−22, −4)` (τ1, strip −26) | `(−22, −3/2)` (τ1, strip −47/2) | `(−22, −4)` (τ0) |
| `B` | `(−79/2, 0)` (τ2) | `(−37, 0)` (τ2) | `(−79/2, 0)` (τ1) |
| `A` | `(38, 0)` | `(71/2, 0)` | `(38, 0)` |
| `z` | `(−16, 5/2)` | `(−16, 19/4)` | `(−16, 5/2)` |

Common data: nook corners `k0 = (2, 34)`, `k1 = (4, 34)`; nook floor
`nf0 = (W_r k0) ∩ (A_r k1)`, `nf1 = (W_l k0) ∩ (A_l k1)` (`_l`, `_r` segment ends), nook vertices
`n0`, `n1` on the line `nf0 nf1` at `x = 2`, `4` (`ge`/`orient`: `n0 = (2, 1020/29)`,
`n1 = (4, 1024/29)`; `le`: `(2, 3910/111)`, `(4, 3916/111)`); stationary guard `g = (−15, 16)`
(a convex vertex, stub `zg = (−12, 157/10)`, slope `−1/10`) with two V-slots on the pillar top
`e_l e_i` aimed at `x = 9/4` and `x = 39/4` (Section 5 `_slot_on_edge`, depth `1/20`, width
`1/400`; tips `qa = (249/80, 409/40)`, `qb = (879/80, 409/40)`); top `y = 34`, `TL = (−4, 34)`,
`RT = A_bay.right_rim + (2, ·)` at height 34.  `orient`: the guard `p` is a convex vertex at the
end of the edge `z → (p − (1, −1/2))` carrying its two slots (depth `1/40`).

Boundary order of the template chain:

```
bay(B), bay(W), z,
  [ge, le]   bay(C), (C_bay.right_rim.x + 1/8, 0)
  [orient]   slot_a(p), slot_b(p), p − (1, −1/2), p, (1/8, 0)
e_l, slot(g, 9/4), slot(g, 39/4), e_i, bay(A), RT, k1, n1, n0, k0, TL, zg, g, e_j
```

The vertex `z` separates `W` from the mechanism: it is above every line from `W` to the
γ-region (so `W` never helps there), below every line from `W` to the nook (so `W` sees `Q`),
below `C`'s strip and below `B`'s lowest sight lines.  Exact slack of these conditions (template
units): `ge`, `orient` 0.32, `le` 0.51.

### 3.3 Inversion template `InvBP`

AAM's mechanism (Section 5 inversion template: `ξ0…ξ3`, `f0…f3`, `g_s`, `z'`,
`n_R`, `n_L`) unchanged; `r_i = (1/2, 0)` (right-oriented, τ = 1) and `r_j = (139/10, 1/10)`
(left-oriented, τ = 0) get bays; the far witnesses of `r_j` are gone; slot `b` of `g_s` is
recomputed on the edge `ξ1 → left shoulder of r_j's bay`.  Chain:
`bay(r_i), ξ0, slot_a, ξ1, slot_b, bay(r_j), g_s, z', ξ3, n_R, n_L, ξ2`.

### 3.4 Canonical guards

For a solution `x`: base guards `(x_i + d_i, 0)` as in Section 5; per unit the corridor
stationary guards, the receivers at their corridor offsets, `A` at the offset of `W`, the
template stationary guards (`g`, and `p` for `orient`).  All lie on `∂P`: segment guards on bay
floors, stationary guards at convex vertices.  `g` is the Section 5 number (e.g. 46, 97, 108, 159 on
small instances).

### 3.5 Pinning and counting with boundary guards

Positions: per bay the segment (`one`: the point `x0 + 1/2`), per stationary guard the point.
Witnesses: `w1`, `w2` (`o1`, `o2`) per bay; the two slot tips per stationary guard.
Main (private) witness: `w1`, resp. the first slot.  With `Ω = ∂P` the conditions of
`Polygon.guards_pinned` hold with **all ranks equal**:

* (spot) a point of `∂P` seeing all witnesses of `X` lies in `X`;
* (late, for all pairs) no point of `∂P` sees the main witness of `Y` and any witness of
  `X ≠ Y`.

---

## 4. What is new compared with Section 5 (proof obligations)

| part | Section 5 | boundary-point |
|---|---|---|
| main area, corridors, parameters, `unit_specs`, `g`, `d_i` | — | unchanged |
| base pockets (`MainArea/Pocket`, `MainArea/Witness`) | 2-D pinning in a pocket | bay lemma (generic, 1-D pinning on `∂P`) |
| template receivers | pockets, far witnesses | bays |
| addition templates | `r'_i` copies `r_i` (τ-max) | `A` copies `W` (τ1; `orient`: τ0); new coordinates |
| inversion template | — | bays only |
| counting | `PosSys.OK` over `p ∈ P.filled`, ranks | `PosSys.OK` over `p ∈ Ω`; `Ω = ∂P` |
| correspondence | guard sets | guard sets on the boundary |

---

## 5. Lean files

The boundary-point hardness proof is in `ArtGallery/Hardness/BP/` and the membership proof in
`ArtGallery/FewVars/BoundaryPoint*` (79 files, 33,169 lines including generated
certificate files). The Section 5 corridors (`Hardness/Sec5/Corridor/*`), the main-area hexagon
lemmas, the template tools and mechanisms, the visibility library `Vis/*` (with the counting
lemmas of `Vis/Pinning.lean` and `Sec5/CountAbstract.lean` generalized to an allowed set `Ω` of
guard positions; Section 5 uses `Ω = P.filled`, the boundary-point proof `Ω = ∂P`) and
`PTime/ETRtoINV` are reused unchanged. The generated files (template data and certificates)
were produced by programs that are not included in this repository; they, and the channel
certificate data (`BP/CoverChanData.lean`), are checked by `decide +kernel`.

| file | lines | content |
|---|---:|---|
| `Hardness/BP/Assemble.lean` | 33 | Boundary-point variant: the assembly of the global polygon |
| `Hardness/BP/Assemble/Bays.lean` | 347 | Boundary-point variant: the receiver bays of the templates |
| `Hardness/BP/Assemble/Check.lean` | 106 | Boundary-point variant: `constructBP` agrees with the reference vertex lists |
| `Hardness/BP/Assemble/Construct.lean` | 113 | Boundary-point variant: the global polygon `constructBP Φ n` |
| `Hardness/BP/Assemble/Global.lean` | 380 | Boundary-point variant: the global polygon is simple, given simple units |
| `Hardness/BP/Assemble/MainGlobal.lean` | 449 | Boundary-point variant: the main area of the global polygon |
| `Hardness/BP/Assemble/PTime.lean` | 154 | Boundary-point variant: the construction is polynomial-time |
| `Hardness/BP/Assemble/RefDataA.lean` | 247 | Boundary-point variant: reference vertex list `refBPA` (data) |
| `Hardness/BP/Assemble/RefDataB.lean` | 353 | Boundary-point variant: reference vertex list `refBPB` (data) |
| `Hardness/BP/Assemble/RefDataC.lean` | 573 | Boundary-point variant: reference vertex list `refBPC` (data) |
| `Hardness/BP/Assemble/Sep.lean` | 252 | Boundary-point variant: the template hypotheses `ChainAt` / `SepAt` for the units |
| `Hardness/BP/Assemble/Side.lean` | 469 | Boundary-point variant: where the units sit in a polygon, clearance |
| `Hardness/BP/Assemble/Sides.lean` | 212 | Boundary-point variant: the two sides of the global polygon |
| `Hardness/BP/Assemble/Simple.lean` | 152 | Boundary-point variant: the polygon `constructBP Φ n` is simple |
| `Hardness/BP/Assemble/TmplData.lean` | 165 | Boundary-point variant: the gadget template chains (data) |
| `Hardness/BP/Assemble/TmplFacts.lean` | 236 | Boundary-point variant: the placed template chains (simplicity and position) |
| `Hardness/BP/Assemble/UnitChain.lean` | 424 | Boundary-point variant: the chain of one unit is simple |
| `Hardness/BP/Bay.lean` | 672 | Boundary-point variant: bays |
| `Hardness/BP/BayCover.lean` | 314 | Boundary-point variant: coverage of a bay |
| `Hardness/BP/Constraint.lean` | 20 | Boundary-point variant: constraints — facts (iv) and (v) with guards on the boundary (umbrella) |
| `Hardness/BP/ConstraintGlobal.lean` | 485 | Boundary-point variant, constraints (iv)+(v): a guard set of size `g` on the boundary encodes a |
| `Hardness/BP/ConstraintKinds.lean` | 492 | Boundary-point variant, constraints (v): the relation enforced by one unit |
| `Hardness/BP/ConstraintUnit.lean` | 410 | Boundary-point variant, constraints: the guards of one unit |
| `Hardness/BP/Count.lean` | 15 | Boundary-point variant: counting — facts (ii) and (iii) with guards on the boundary (umbrella) |
| `Hardness/BP/CountGlobal.lean` | 336 | Boundary-point variant, counting: facts (ii) and (iii) for the global polygon |
| `Hardness/BP/CountSide.lean` | 145 | Boundary-point variant, counting: the units of a side |
| `Hardness/BP/CountUnit.lean` | 385 | Boundary-point variant, counting: the positions of one unit |
| `Hardness/BP/Cover.lean` | 29 | Boundary-point variant: coverage by the canonical guards |
| `Hardness/BP/CoverCanon.lean` | 189 | Boundary-point variant: the canonical guards of an assignment |
| `Hardness/BP/CoverChanData.lean` | 66 | Boundary-point variant: the channel certificates of the four templates |
| `Hardness/BP/CoverGlob.lean` | 167 | Boundary-point variant, coverage: the pieces of the region of the global polygon |
| `Hardness/BP/CoverKind.lean` | 250 | Boundary-point variant, coverage: the template facts by kind |
| `Hardness/BP/CoverMain.lean` | 212 | Boundary-point variant: the canonical guards see the whole polygon |
| `Hardness/BP/CoverRegion.lean` | 303 | Boundary-point variant, coverage: the region of the global polygon is the union of its pieces |
| `Hardness/BP/CoverSide.lean` | 327 | Boundary-point variant, coverage: the vertical lines of the sides, special edges |
| `Hardness/BP/CoverUnit.lean` | 576 | Boundary-point variant, coverage: the pieces of a unit |
| `Hardness/BP/CoverUnitLocal.lean` | 537 | Boundary-point variant, coverage: the unit region is a room with the entrance as door |
| `Hardness/BP/Main.lean` | 161 | ETR reduces in polynomial time to `AGPBoundaryPoint` |
| `Hardness/BP/MainArea.lean` | 286 | Boundary-point variant: the bottom wall with bays (definitions, placement) |
| `Hardness/BP/MainAreaBottom.lean` | 227 | Boundary-point variant: the bottom wall with bays is a simple chain |
| `Hardness/BP/MainAreaCheck.lean` | 133 | Boundary-point variant: the bottom wall agrees with the reference vertex lists |
| `Hardness/BP/MainAreaCount.lean` | 133 | Boundary-point variant, counting: the base positions (main area) |
| `Hardness/BP/MainAreaHex.lean` | 236 | Boundary-point variant: the main hexagon is seen by the base guards |
| `Hardness/BP/MainAreaRoom.lean` | 521 | Boundary-point variant: the room of a base bay and its coverage |
| `Hardness/BP/PTime/Construct.lean` | 158 | The Section 5 construction is polynomial-time |
| `Hardness/BP/PTime/Corridor.lean` | 406 | Polynomial time of the Section 5 construction: corridors |
| `Hardness/BP/PTime/Encode.lean` | 82 | Polynomial time of the instance code of a rational polygon |
| `Hardness/BP/PTime/Params.lean` | 379 | Polynomial time of the Section 5 construction: parameters, main area, template data |
| `Hardness/BP/PTime/Tools.lean` | 236 | Polynomial-time tools for the Section 5 construction |
| `Hardness/BP/Templates/AddGE.lean` | 313 | Boundary-point templates: the addition template `AddBP ge` (`u_W + u_B ≥ u_C`) — template facts |
| `Hardness/BP/Templates/AddGECert.lean` | 443 | Boundary-point templates: the addition template `AddBP ge` (`u_W + u_B ≥ u_C`) — generated certificates |
| `Hardness/BP/Templates/AddGECover.lean` | 197 | Boundary-point templates: the addition template `AddBP ge` (`u_W + u_B ≥ u_C`) — coverage by the canonical guards (T-cover) |
| `Hardness/BP/Templates/AddGECoverCert.lean` | 1089 | Boundary-point templates: T-cover certificates of `AddGE` — visibility of the pieces (generated) |
| `Hardness/BP/Templates/AddGECoverData.lean` | 1377 | Boundary-point templates: the addition template `AddBP ge` (`u_W + u_B ≥ u_C`) — T-cover certificates (generated) |
| `Hardness/BP/Templates/AddGEData.lean` | 938 | Boundary-point templates: the addition template `AddBP ge` (`u_W + u_B ≥ u_C`) — generated data |
| `Hardness/BP/Templates/AddLE.lean` | 313 | Boundary-point templates: the addition template `AddBP le` (`u_W + u_B ≥ u_C + 5/2`) — template facts |
| `Hardness/BP/Templates/AddLECert.lean` | 443 | Boundary-point templates: the addition template `AddBP le` (`u_W + u_B ≥ u_C + 5/2`) — generated certificates |
| `Hardness/BP/Templates/AddLECover.lean` | 228 | Boundary-point templates: the addition template `AddBP le` (`u_W + u_B ≥ u_C + 5/2`) — coverage by the canonical guards (T-cover) |
| `Hardness/BP/Templates/AddLECoverCert.lean` | 834 | Boundary-point templates: T-cover certificates of `AddLE` — visibility of the pieces (generated) |
| `Hardness/BP/Templates/AddLECoverData.lean` | 1100 | Boundary-point templates: the addition template `AddBP le` (`u_W + u_B ≥ u_C + 5/2`) — T-cover certificates (generated) |
| `Hardness/BP/Templates/AddLEData.lean` | 938 | Boundary-point templates: the addition template `AddBP le` (`u_W + u_B ≥ u_C + 5/2`) — generated data |
| `Hardness/BP/Templates/BdTools.lean` | 459 | Boundary-point templates: pinning on the boundary |
| `Hardness/BP/Templates/CountAddGE.lean` | 1106 | Boundary-point templates: the addition template `AddBP ge` (`u_W + u_B ≥ u_C`) — counting facts on the boundary |
| `Hardness/BP/Templates/CountAddLE.lean` | 1106 | Boundary-point templates: the addition template `AddBP le` (`u_W + u_B ≥ u_C + 5/2`) — counting facts on the boundary |
| `Hardness/BP/Templates/CountInv.lean` | 489 | Boundary-point templates: the inversion template — counting facts on the boundary |
| `Hardness/BP/Templates/CountOrient.lean` | 1069 | Boundary-point templates: the orientation template `AddBP orient` (`u_W + u_B ≥ 5/2`) — counting facts on the boundary |
| `Hardness/BP/Templates/Inv.lean` | 79 | Boundary-point templates: the inversion template `x_a · x_b = 1` — template facts |
| `Hardness/BP/Templates/InvCover.lean` | 218 | Boundary-point templates: the inversion template — coverage (T-cover) |
| `Hardness/BP/Templates/InvCoverData.lean` | 1013 | Boundary-point templates: the inversion template — T-cover certificates (generated) |
| `Hardness/BP/Templates/InvData.lean` | 737 | Boundary-point templates: the inversion template — generated data |
| `Hardness/BP/Templates/InvMech.lean` | 520 | Boundary-point templates: the inversion template — the mechanism (paper Lemmas 49/50) |
| `Hardness/BP/Templates/Orient.lean` | 313 | Boundary-point templates: the orientation template `AddBP orient` (`u_W + u_B ≥ 5/2`) — template facts |
| `Hardness/BP/Templates/OrientCert.lean` | 448 | Boundary-point templates: the orientation template `AddBP orient` (`u_W + u_B ≥ 5/2`) — generated certificates |
| `Hardness/BP/Templates/OrientCover.lean` | 201 | Boundary-point templates: the orientation template `AddBP orient` (`u_W + u_B ≥ 5/2`) — coverage by the canonical guards (T-cover) |
| `Hardness/BP/Templates/OrientCoverCert.lean` | 1059 | Boundary-point templates: T-cover certificates of `Orient` — visibility of the pieces (generated) |
| `Hardness/BP/Templates/OrientCoverData.lean` | 1337 | Boundary-point templates: the orientation template `AddBP orient` (`u_W + u_B ≥ 5/2`) — T-cover certificates (generated) |
| `Hardness/BP/Templates/OrientData.lean` | 898 | Boundary-point templates: the orientation template `AddBP orient` (`u_W + u_B ≥ 5/2`) — generated data |
| `FewVars/BoundaryPointMain.lean` | 43 | The boundary-point art gallery problem is in `∃ℝ`, with only guard variables |
| `FewVars/BoundaryPoint/Formula.lean` | 308 | The formula for the boundary-point art gallery problem |

Main statements: `constructBP_simple`, `count_lowerBP`, `count_pinnedBP`,
`Constraint.guardSet_solutionBP`, `canonGuardsBP_guard`, `canonGuardsBP_card`,
`sat_iff_hasGuardSetOnBoundaryOfCard`, `etr_polyRed_agpBoundaryPoint'`, and in `ArtGallery`:
`agpBoundaryPoint_erComplete`, `agpBoundaryPoint_inER_guard_variables`.

## 6. Notes on the proof

* **Counting on `∂P`.** The two spike triangles of a bay overlap in the plane; only boundary
  points seeing both tips are pinned to the floor (`Bay.lean`, `spot_bay`). The 2-D visibility
  regions of all witnesses lie in the bay boxes, so the disjointness conditions of the counting
  lemmas hold in the whole plane.
* **Bay rooms.** Horizontal sections of a bay room are not intervals (there is a gap between
  each spike and its wall), so the room argument uses vertical, horizontal and slope `±1/16` rays.
* **Channel separation.** For the new addition templates the line `x + y = const` that separates
  the two channel walls in Section 5 does not separate them; a determinant argument replaces it
  (`Assemble/UnitChain.lean`).
* **Channel certificates.** The certificates showing that each receiver sees the corridor window
  are recomputed for the new templates; for `inv` the chain edge next to the upper end of the
  mouth needs one extra separating line.
* **Template coverage.** The cover certificates use additional nearly horizontal free rays and
  anchors beyond each spike tip to certify the notch between a bay wall and its spike.
* **Margins.** Some template margins are small (the separating vertex `z`: slack 0.32 template
  units in `ge`/`orient`; spike heights `1/128 … 1/16`); all checks are exact.
