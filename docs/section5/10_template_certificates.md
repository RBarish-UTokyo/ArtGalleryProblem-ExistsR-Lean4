# 10 — Template certificates (Lean: `ArtGallery/Hardness/Sec5/Templates/`)

The gadget lemmas of §7 of `08_proof_plan.md`, proved by certified computation.  All files build,
no `sorry`, `#print axioms` of every main theorem = `[propext, Classical.choice, Quot.sound]`;
kernel checks are `decide +kernel` on ℤ data (no `native_decide`).

## Files

| file | content | written |
|---|---|---|
| `Tools.lean` | `ChainAt`, `Region`, `SepAt`, all certificate checkers + soundness lemmas | hand |
| `InvData.lean` | `Inv` data, separator pieces, W1-converse (`inv_sees_*`), W3 (`inv_w3_*`), visibility characterisations on the zones | generated |
| `InvMech.lean` | guards `invGp x`, `invGq y`; umbra / nook identities; `inv_umbra_iff`, `inv_nook_iff` | hand |
| `Inv.lean` | `invPT` (template polygon) satisfies the hypotheses; W1 (`inv_spot_*`), W2 (`inv_w2_*`) | hand |
| `AddCommon.lean` | `segGuard`, bilinear interpolation, abstract `Γ` lemmas (`gamma_cover`, `gamma_gap`), weak-copy nook (`copyNook_iff`, via `Corridor.CopyPair`) | hand |
| `AddGEData/AddGECert/AddGE.lean` | `Add ge` (data / visibility certificates, W1-converse, W3, exclusivity / mechanism, W1, W2) | generated |
| `AddLEData/AddLECert/AddLE.lean` | `Add le` | generated |
| `OrientData/OrientCert/Orient.lean` | `Add orient` (prefix `addOR`) | generated |

## Statement conventions

* Template coordinates are integers: `Z = D · T` (`T` = coordinates of `07_template_vertices.md`),
  `D` = `invD = 501495790400`, `addGED = 83197200`, `addLED = 24738000`, `addORD = 148879200`.
* Every lemma is about an **arbitrary** polygon `P` with
  * `P.Simple`, `P.InteriorLeft`;
  * `ChainAt P V a`: the template chain `V` (scaled) occurs as consecutive vertices
    `a, a+1, …` of `P`;
  * (only where needed) `SepAt P V a R`: no edge of `P` other than the chain edges meets the
    region `R` = open box `|x|, |y| < 60 D` minus two thin closed wedges ("zones") with apex at the
    chain ends, `x ≤ apex.x`, bounded by the line `x + y = apex.x + apex.y` (the channel
    direction) and a line of slope `−101/100` or `−99/100` through the apex.  The channel walls
    of the unit lie in these wedges:
    * first zone (apex `V₀`, all kinds): `x + y ≥ s₀`, `101x + 100y ≤ 101 V₀.x + 100 V₀.y`
      (`s = apex.x + apex.y`);
    * second zone (apex `V_l`), `Inv`: `x + y ≤ s_l`, `99x + 100y ≥ 99 V_l.x + 100 V_l.y`;
    * second zone, the three addition kinds (`addGER`, `addLER`, `addORR`): `x + y ≥ s_l`,
      `101x + 100y ≤ 101 V_l.x + 100 V_l.y` (same shape as the first zone).  Here
      `V_l = e_j = (−10, 21/2)` and the upper wall runs in direction `(−S + 10, S − 9)`, along
      which `x + y` *increases* (by 1 per unit parameter) and `101x + 100y` decreases (by
      `S − 110`).  The generic wedge of `Inv` (`x + y ≤ s_l`) would not contain this
      wall.
* The template polygon `P_T = chain ++ stub` (stub vertices `(−100, v_last.x + v_last.y + 100)`,
  `(−100, v_0.x + v_0.y + 100)`, times `D`) satisfies all four hypotheses (`invPT_simple/_ccw/_chain/_sep`,
  `addGEPT_*`, …), so the lemmas are not vacuous.
* Guards with real values: `Inv`: `invGp x = (D x, 0)`, `invGq y = (D (159/10 − y), D/10)`;
  `Add`: `segGuard A B u` = point of the guard segment `[A, B]` with value `u` (left end value `1/2`,
  position linear in `u`): `addXA` on `r'_i`, `addXB` on `r_j`, `addXC` on `r_l` (`orient`: the
  stationary guard point `p`), `addXI` on `r_i`.
* Zones: `invZu` (quadrilateral in the umbra containing all critical points), `invZn` (segment of
  the nook axis containing all critical points), `addXZg` (quadrilateral in `Γ` containing all crossing
  points `γ(u, v)`, `u, v ∈ [1/2, 5/2]`), `addXZn` (segment of the weak-copy nook axis).

## Main theorems (T-mech)

```
inv_umbra_iff (hP) (hL) (hC : ChainAt P invV a) (hS : SepAt P invV a invR) {x y : ℝ}
    (1/2 ≤ x ≤ 2) (1/2 ≤ y ≤ 2) :
  (∀ z ∈ convexHull ℝ (intSet invZu), 0 < invLu.val z → P.Sees (invGp x) z ∨ P.Sees (invGq y) z)
    ↔ x * y ≤ 1
inv_nook_iff … : (∀ w ∈ convexHull ℝ (intSet invZn), P.Sees (invGp x) w ∨ P.Sees (invGq y) w) ↔ 1 ≤ x * y
addGE_gamma_iff … {u v w} (u, v, w ∈ [1/2, 2]) :
  (∀ z ∈ convexHull ℝ (intSet addGEZg), P.Sees (addGEA u) z ∨ P.Sees (addGEB v) z ∨ P.Sees (addGEC w) z)
    ↔ w ≤ u + v
addLE_gamma_iff … ↔ w + 5/2 ≤ u + v
addOR_gamma_iff … {u v} : (… ∨ P.Sees addORC z) ↔ 5/2 ≤ u + v
addGE_nook_iff … {u u'} (u, u' ∈ [1/2, 2]) :
  (∀ z ∈ convexHull ℝ (intSet addGEZn), P.Sees (addGEI u) z ∨ P.Sees (addGEA u') z) ↔ u' ≤ u
(same: addLE_nook_iff, addOR_nook_iff)
```

Also `inv_umbra_cover/gap`, `inv_nook_cover/gap` (the two directions separately), `X_gamma_id`
(projection identity, paper Lemma 41), exclusivity `X_excl_Zg_*`, `X_excl_Zn_*` (no other guard
segment / stationary guard sees the zones).

## W1 / W2 / W3 (T-cones, T-W1, T-W2/W3)

* `X_cone`: a point seeing a witness `cv V j` (`j ∈ XWit`) lies in its cone.
* W1: `X_spot_r` (a point seeing the four witnesses of the guard segment `r` lies on `r`),
  `X_spot_g` (stationary guards); converse `X_sees_*` (every point of the segment sees its witnesses).
* W2: `X_w2_r_s`: no point sees witnesses of two different segments (one witness each, via rooms
  of the pockets `XK*` and cone half-planes; for the vertical-edge cases `sees_side_of_crossVert`).
* W3: `X_w3_r_w`: no point of segment `r` sees a witness `w` of another segment.

## Certificate types (`Tools.lean`)

`crossB` (segment family crosses a chain edge properly), `halfB` (half-crossing at a shadow
corner), `gateB` (two convex pieces joined through a gate), `pieceB` + `Region.check(F)` (convex
pieces of `filled P` near the chain, with Farkas combinations), `outConeB`, `horizBetweenB` (vertex on a
collinear segment), `spotB`, `sgB`, `conesB`, `rayOKB` / `crossVertB`, `coneHPB`, `stubOutB`,
`lowB`, `supportB`.

## Design changes made for the certificates

Recorded in `05_gadgets.md` and `07_template_vertices.md` ("Changes for the certificates"):
1. `Inv`, pocket `r_j`: the left mouth corner moved to `(r_j.x − 2, r_j.y + 3/5)` (the old corner
   `(11.9, 1.1)` lay above the sight line from `q(2)` to `ξ1`, so for `y ∈ (1.58, 2]` the guard `q`
   was blind to part of the umbra — a design error, not a paper error).
2. Slot corners re-placed on the grid `1/400` (floor corners at most `1/200` below), so `D` stays
   moderate.
3. `Add le`: the `z` block moved from `(−25/2, −1/10)` to `(−13, −2/5)` (`r_i` at value `1/2` saw
   a corner of `Γ`).

## What the assembly supplies (U1/U2)

For a unit with similarity `φ(z) = m + z / (S·D)` (or mirror ∘ φ, with the chain reversed):
1. `ChainAt P (V.map φ⁻¹-scaled) a`: the unit's chain occurs contiguously in the global polygon —
   in practice: state the template lemmas for `P' := φ⁻¹(P)`; `Sees`, `Simple`, `InteriorLeft`,
   `convexHull` commute with the similarity (`det` scales by a positive factor).
2. `SepAt P' V a R`: inside the box `|x|, |y| < 60` (template units) around the unit, the only
   global edges besides the chain are the two channel walls, and these lie in the wedges, i.e.
   their direction differs from `(−1, 1)` by slope `< 1/100` on the correct side — holds when
   `S ≥ 10^4` (lower wall direction `(−S − V₀.x, S − V₀.y)`, upper wall direction
   `(−S − V_l.x, S + 3/2 − V_l.y)`); the box must contain no other unit.  **Done** in
   `Assemble/Sep.lean`: `lowerWall_zone`, `upperWall_zone` (all four kinds) and
   `SideAt.sepAt` (every unit of either side, no extra hypothesis).
3. Cross-unit W2/W3 (witnesses of different units) are proved in `Count*.lean`, the
   window/channel lemma U2 in `CoverChan*.lean`, and the coverage of the rest of the template
   room by the canonical guards (T-cover, §9) in `Templates/*Cover*.lean`.  The `*_iff` lemmas
   cover the zones that contain all critical points.
