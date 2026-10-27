# 08 — Proof structure for Theorem 54 (Section 5)

## 0. The statement of Theorem 54

Read literally, the paper's Theorem 54 is false for `n ≥ 2` (see `docs/paper_issues.md`, A2): let
`G` be a guard set of cardinality `g` and let `(u, 0) ∈ G` be the guard of the representative of
variable 1, i.e. `u = x̂_1 + d_1` for the value `x̂_1 ∈ [1/2,2]`.  Put `x_1 := x̂_1`,
`x_0 := u − d_0` and `x_i := x̂_i` otherwise.  Then `(x_i + d_i, 0) ∈ G` for all `i` (for `i = 0`
and `i = 1` it is the same point), so "some guard set of cardinality `g` contains the guards
`(x_i + d_i, 0)`" holds, but `x_0 = x̂_1 + (d_1 − d_0) ∉ [1/2, 2]` because the guard segments of
different variables are disjoint.  The paper implicitly quantifies over `x ∈ [1/2,2]^n`.

The formal statement (`etrinv_guard_correspondence`) therefore has the range condition on both
sides of the equivalence:
```lean
∀ x : ℕ → ℝ,
  ((∀ i < n, 1/2 ≤ x i ∧ x i ≤ 2) ∧ ∀ c ∈ Φ, c.Holds x) ↔
    (∀ i < n, 1/2 ≤ x i ∧ x i ≤ 2) ∧
    ∃ G : Finset Point, G.card = g ∧ P.IsGuardSet G ∧ ∀ i < n, (x i + d i, 0) ∈ G
```
With the range, the point `(x_i + d_i, 0)` lies on the representative segment
`s_i = [d_i + 1/2, d_i + 2] × {0}`, which no other guard position meets, so it *is* the guard of
`s_i`.  The conjunct "every `g`-guard set contains `(x_i + d_i, 0)` for some solution `x`" is
true as stated and is what Theorem 55 uses.

## 1. Global structure of the proof

```
construct : List Constraint → ℕ → List (ℚ×ℚ)          (computable, lists/ℕ/ℚ only)
guardCount, shift d i = 27 i/2 − 1/2
(i)   Simple                                          [Sec5/Simple*]
(ii)  every guard set has ≥ g guards                   [Sec5/Count]
(iii) a g-guard set has exactly one guard on every guard segment and at every stationary point,
      and no other guard                               [Sec5/Count]
(iv)  copies: guard on base slot σ and guard on its receiver specify the same value
                                                       [Sec5/CorridorCopy]
(v)   gadget constraints hold for the specified values [Sec5/Gadget*]
(vi)  sufficiency: canonical guards of a solution see everything
                                                       [Sec5/Cover*]
(vii) correspondence d_i, card = g of the canonical set, assembly
                                                       [Sec5/Main]
```
`n = 0`: triangle, `g = 1` (separate 30-line file).

The geometry is organised so that every non-trivial geometric statement is one of:
* **cone facts** (`03`, T1'): `Sees v p → p ∈ cone_v` for a convex vertex `v`;
* **room facts** (T4): leaving a room crosses its door;
* **crossing facts** (T1): an explicit edge is properly crossed — two sign conditions on `det`;
* **convex-piece facts** (T2): an explicit convex polygon (given by ≤ 8 half-planes) contains the
  segment and its interior meets no edge.
All of them reduce to finitely many polynomial (mostly linear) inequalities in the parameters
`S = 200000·N²`, `H = S+3m+1`, slot abscissae `27σ/2`, and fixed template rationals.

## 2. Lean files

Section 5 lives in `ArtGallery/Hardness/Sec5/` (125 files, 55,758 lines including the generated
certificate files); the general visibility library it uses is `ArtGallery/Vis/`.  Generated files
(`Templates/*Data.lean`, `*Cert.lean`, `*CoverData.lean`, `CountTmpl*.lean`, `Assemble/RefData*.lean`,
`Assemble/TmplData.lean`) were produced by programs that are not included in this repository;
the Lean kernel checks them like every other file.

| file | lines | content |
|---|---:|---|
| `Hardness/Sec5/Assemble.lean` | 19 | Section 5: the global polygon (umbrella) |
| `Hardness/Sec5/Assemble/Bottom.lean` | 238 | Section 5: the bottom wall is a simple chain (08 §4, Lemma S3) |
| `Hardness/Sec5/Assemble/Check.lean` | 160 | Section 5: `construct` agrees with the reference vertex lists |
| `Hardness/Sec5/Assemble/Clear.lean` | 416 | Section 5: clearance of a unit in its polygon |
| `Hardness/Sec5/Assemble/Comb.lean` | 188 | Section 5: units hanging from a vertical line (comb lemma) |
| `Hardness/Sec5/Assemble/Construct.lean` | 124 | Section 5: the global polygon `construct Φ n` |
| `Hardness/Sec5/Assemble/Entrance.lean` | 139 | Section 5: the corridor polygon near the line `x = S` |
| `Hardness/Sec5/Assemble/Global.lean` | 398 | Section 5: the global polygon is simple, given simple units (08 §4, Lemmas S1/S2) |
| `Hardness/Sec5/Assemble/Glue.lean` | 381 | Section 5: gluing simple chains (generic tools) |
| `Hardness/Sec5/Assemble/Placement.lean` | 145 | Section 5: where the units sit in a polygon (generic) |
| `Hardness/Sec5/Assemble/RefData.lean` | 914 | Section 5: reference vertex lists (data) |
| `Hardness/Sec5/Assemble/RefDataC.lean` | 904 | Section 5: reference vertex lists (data, instance C) |
| `Hardness/Sec5/Assemble/Sep.lean` | 281 | Section 5: the template hypotheses `ChainAt` / `SepAt` for the units |
| `Hardness/Sec5/Assemble/Sides.lean` | 232 | Section 5: the two sides of the global polygon |
| `Hardness/Sec5/Assemble/Simple.lean` | 266 | Section 5: the polygon `construct Φ n` is simple (08 §4) |
| `Hardness/Sec5/Assemble/TmplData.lean` | 140 | Section 5: the gadget template chains (data) |
| `Hardness/Sec5/Assemble/TmplFacts.lean` | 281 | Section 5: the placed template chains (simplicity and position) |
| `Hardness/Sec5/Assemble/UnitChain.lean` | 404 | Section 5: the chain of one unit is simple (08 §4, Lemma S4) |
| `Hardness/Sec5/Constraint.lean` | 25 | Section 5: constraints — facts (iv) and (v) of `08_proof_plan.md` §1 (umbrella) |
| `Hardness/Sec5/ConstraintCopy.lean` | 305 | Section 5, constraints (iv): the corridor copies values exactly |
| `Hardness/Sec5/ConstraintGlobal.lean` | 365 | Section 5, constraints (iv)+(v): a guard set of size `g` encodes a solution |
| `Hardness/Sec5/ConstraintKinds.lean` | 271 | Section 5, constraints (iv)+(v) for one unit |
| `Hardness/Sec5/ConstraintSide.lean` | 115 | Section 5, constraints: the guards of a side |
| `Hardness/Sec5/ConstraintTmpl.lean` | 266 | Section 5, constraints (v): the mechanism of the four templates |
| `Hardness/Sec5/ConstraintTools.lean` | 536 | Section 5, constraints (iv)/(v): tools |
| `Hardness/Sec5/ConstraintUnit.lean` | 411 | Section 5, constraints: the guards of one unit |
| `Hardness/Sec5/Corridor/Bounds.lean` | 394 | Section 5: corridors — bounds on the corridor vertices |
| `Hardness/Sec5/Corridor/Chain.lean` | 886 | Simple polylines |
| `Hardness/Sec5/Corridor/Coords.lean` | 387 | Section 5: corridors — local coordinates of the corridor vertices |
| `Hardness/Sec5/Corridor/Copy.lean` | 536 | Section 5: corridors — the exact copy algebra (Lemmas 27/28 generalised) |
| `Hardness/Sec5/Corridor/CopyCorridor.lean` | 470 | Section 5: corridors — the copy algebra for the corridor's umbras and nooks |
| `Hardness/Sec5/Corridor/Cover.lean` | 207 | Section 5: corridors — the canonical guards cover the corridor |
| `Hardness/Sec5/Corridor/CoverBase.lean` | 328 | Section 5: corridors — the base guards see the umbra through the entrance |
| `Hardness/Sec5/Corridor/CoverClassA.lean` | 204 | Section 5: corridors — locating the interior points of the corridor (preparation) |
| `Hardness/Sec5/Corridor/CoverClassB.lean` | 330 | Section 5: corridors — locating the interior points of the corridor above the floor |
| `Hardness/Sec5/Corridor/CoverFacts.lean` | 426 | Section 5: corridors — facts for the coverage proof |
| `Hardness/Sec5/Corridor/CoverNook.lean` | 217 | Section 5: corridors — the copy guards see the umbra and the nook |
| `Hardness/Sec5/Corridor/CoverRecv.lean` | 193 | Section 5: corridors — the receivers see the umbra through the window |
| `Hardness/Sec5/Corridor/CoverRecvA.lean` | 187 | Section 5: corridors — the receiver's view of the umbra (preparation) |
| `Hardness/Sec5/Corridor/CoverRecvB.lean` | 279 | Section 5: corridors — the receiver's view of the umbra (cone and valley facts) |
| `Hardness/Sec5/Corridor/CoverRecvC.lean` | 251 | Section 5: corridors — the receivers see the umbra through the window (main lemma) |
| `Hardness/Sec5/Corridor/CoverRecvD.lean` | 159 | Section 5: corridors — the receivers see the umbra through the window |
| `Hardness/Sec5/Corridor/CoverSeg.lean` | 360 | Section 5: corridors — tools for the sight segments of the copy guards |
| `Hardness/Sec5/Corridor/CoverSlotA.lean` | 224 | Section 5: corridors — the floor slots (pieces) |
| `Hardness/Sec5/Corridor/CoverSlotB.lean` | 150 | Section 5: corridors — the slot pieces lie in the corridor region |
| `Hardness/Sec5/Corridor/CoverSlotC.lean` | 303 | Section 5: corridors — the floor slots (visibility and location) |
| `Hardness/Sec5/Corridor/CoverSlotD.lean` | 157 | Section 5: corridors — interior points below the floor line lie in a slot piece |
| `Hardness/Sec5/Corridor/CoverStrip.lean` | 497 | Section 5: corridors — the strips below the axes (coverage, part (a)) |
| `Hardness/Sec5/Corridor/CoverTools.lean` | 238 | Section 5: corridors — generic tools for the coverage proof |
| `Hardness/Sec5/Corridor/CoverUmbra.lean` | 301 | Section 5: corridors — the umbra region and the nook (pieces) |
| `Hardness/Sec5/Corridor/Critical.lean` | 393 | Section 5: corridors — location of the critical sets |
| `Hardness/Sec5/Corridor/Defs.lean` | 516 | Section 5: corridors — definitions |
| `Hardness/Sec5/Corridor/Floor.lean` | 443 | Section 5: corridors — the floor |
| `Hardness/Sec5/Corridor/Member.lean` | 618 | Section 5: corridors — points of the corridor region |
| `Hardness/Sec5/Corridor/NookEdge.lean` | 115 | Section 5: corridors — the nook top edge contains the nook critical segment |
| `Hardness/Sec5/Corridor/Poly.lean` | 313 | Section 5: corridors — the corridor polygon is simple |
| `Hardness/Sec5/Corridor/Receiver.lean` | 189 | Section 5: corridors — the receiver conditions |
| `Hardness/Sec5/Corridor/Room.lean` | 261 | Section 5: corridors — the corridor is a room with two doors |
| `Hardness/Sec5/Corridor/SGView.lean` | 564 | Section 5: corridors — what the stationary guards do not see |
| `Hardness/Sec5/Corridor/Shape.lean` | 603 | Section 5: corridors — the shape of the corridor |
| `Hardness/Sec5/Corridor/Slabs.lean` | 534 | Section 5: corridors — the slab inequalities |
| `Hardness/Sec5/Corridor/Slots.lean` | 398 | Section 5: corridors — the slot witnesses |
| `Hardness/Sec5/Corridor/Stationary.lean` | 389 | Section 5: corridors — the stationary guards |
| `Hardness/Sec5/Corridor/Upper.lean` | 325 | Section 5: corridors — the upper wall is monotone |
| `Hardness/Sec5/Corridor/Visibility.lean` | 303 | Section 5: corridors — the band lemma (Lemma V1) |
| `Hardness/Sec5/Count.lean` | 18 | Section 5: counting — facts (ii) and (iii) of `08_proof_plan.md` §1 (umbrella) |
| `Hardness/Sec5/CountAbstract.lean` | 322 | Section 5, counting (ii)/(iii): positions grouped in zones |
| `Hardness/Sec5/CountCorridor.lean` | 169 | Section 5, counting: the witness slots of different stationary guards of a corridor |
| `Hardness/Sec5/CountGlobal.lean` | 347 | Section 5, counting: facts (ii) and (iii) for the global polygon |
| `Hardness/Sec5/CountMain.lean` | 222 | Section 5, counting: the base positions (main area) |
| `Hardness/Sec5/CountSide.lean` | 217 | Section 5, counting: the units of a side |
| `Hardness/Sec5/CountTmplGE.lean` | 1408 | Section 5, counting: the positions of the template `AddGE` |
| `Hardness/Sec5/CountTmplInv.lean` | 543 | Section 5, counting: the positions of the template `Inv` |
| `Hardness/Sec5/CountTmplLE.lean` | 1401 | Section 5, counting: the positions of the template `AddLE` |
| `Hardness/Sec5/CountTmplOrient.lean` | 1241 | Section 5, counting: the positions of the template `Orient` |
| `Hardness/Sec5/CountTools.lean` | 195 | Section 5, counting: template position systems and certificate tools |
| `Hardness/Sec5/CountUnit.lean` | 407 | Section 5, counting: the positions of one unit |
| `Hardness/Sec5/Cover.lean` | 251 | Section 5, sufficiency (vi): the canonical guards see the whole polygon |
| `Hardness/Sec5/CoverCanon.lean` | 256 | Section 5, sufficiency (vi)/(vii): the canonical guards of an assignment |
| `Hardness/Sec5/CoverChanData.lean` | 402 | Section 5, sufficiency (vi): the channel certificate of a template |
| `Hardness/Sec5/CoverChanKinds.lean` | 54 | Section 5, sufficiency (vi): the channel certificates of the four templates |
| `Hardness/Sec5/CoverChanTools.lean` | 439 | Section 5, sufficiency (vi): tools for the channel of a unit (template coordinates) |
| `Hardness/Sec5/CoverCons.lean` | 134 | Section 5, sufficiency (vi): the canonical values satisfy the template constraints |
| `Hardness/Sec5/CoverGlob.lean` | 203 | Section 5, sufficiency (vi): the pieces of the region of the global polygon |
| `Hardness/Sec5/CoverHex.lean` | 348 | Section 5, sufficiency (vi): the main hexagon |
| `Hardness/Sec5/CoverKind.lean` | 265 | Section 5, sufficiency (vi): the template facts by kind |
| `Hardness/Sec5/CoverMain.lean` | 494 | Section 5, sufficiency (vi): the boundary of the global polygon |
| `Hardness/Sec5/CoverRegion.lean` | 438 | Section 5, sufficiency (vi): the region of the global polygon is the union of its pieces |
| `Hardness/Sec5/CoverSide.lean` | 152 | Section 5, sufficiency (vi): the vertical line of a side |
| `Hardness/Sec5/CoverUnit.lean` | 568 | Section 5, sufficiency (vi): the pieces of a unit |
| `Hardness/Sec5/CoverUnitLocal.lean` | 662 | Section 5, sufficiency (vi): the unit region is a room with the entrance as door |
| `Hardness/Sec5/CoverVtx.lean` | 221 | Section 5, sufficiency (vi): special vertices and edges of the global polygon |
| `Hardness/Sec5/Main.lean` | 177 | Section 5: Theorem 54 |
| `Hardness/Sec5/MainArea.lean` | 281 | Section 5: the main area — pockets, bottom wall, main hexagon (definitions) |
| `Hardness/Sec5/MainArea/Cover.lean` | 548 | Section 5: coverage of the pocket room and of its column of the main hexagon |
| `Hardness/Sec5/MainArea/Pocket.lean` | 385 | Section 5: the pocket polygon |
| `Hardness/Sec5/MainArea/Steep.lean` | 320 | Section 5: effective cones of the shaft witnesses |
| `Hardness/Sec5/MainArea/Witness.lean` | 576 | Section 5: pocket witnesses, the pocket room, the guard-segment lemma |
| `Hardness/Sec5/Params.lean` | 288 | Section 5: parameters of the construction |
| `Hardness/Sec5/Templates/AddCommon.lean` | 175 | Section 5: addition-type templates — common mechanism lemmas |
| `Hardness/Sec5/Templates/AddGE.lean` | 582 | Section 5: the addition template `Add ge` (`x_a + x_b ≥ x_c`) — template facts |
| `Hardness/Sec5/Templates/AddGECert.lean` | 1071 | Section 5: the addition template `Add ge` (`x_a + x_b ≥ x_c`) — generated certificates |
| `Hardness/Sec5/Templates/AddGECover.lean` | 196 | Section 5: the ge template — coverage by the canonical guards (T-cover) |
| `Hardness/Sec5/Templates/AddGECoverCert.lean` | 749 | Section 5: T-cover certificates of `AddGE` — visibility of the pieces (generated) |
| `Hardness/Sec5/Templates/AddGECoverData.lean` | 1029 | Section 5: the ge template — T-cover certificates (generated) |
| `Hardness/Sec5/Templates/AddGEData.lean` | 1222 | Section 5: the addition template `Add ge` (`x_a + x_b ≥ x_c`) — generated data |
| `Hardness/Sec5/Templates/AddLE.lean` | 582 | Section 5: the addition template `Add le` (`u_A + u_B ≥ u_C + 5/2`) — template facts |
| `Hardness/Sec5/Templates/AddLECert.lean` | 1071 | Section 5: the addition template `Add le` (`u_A + u_B ≥ u_C + 5/2`) — generated certificates |
| `Hardness/Sec5/Templates/AddLECover.lean` | 227 | Section 5: the le template — coverage by the canonical guards (T-cover) |
| `Hardness/Sec5/Templates/AddLECoverCert.lean` | 1037 | Section 5: T-cover certificates of `AddLE` — visibility of the pieces (generated) |
| `Hardness/Sec5/Templates/AddLECoverData.lean` | 1453 | Section 5: the le template — T-cover certificates (generated) |
| `Hardness/Sec5/Templates/AddLEData.lean` | 1222 | Section 5: the addition template `Add le` (`u_A + u_B ≥ u_C + 5/2`) — generated data |
| `Hardness/Sec5/Templates/CoverTools.lean` | 663 | Section 5 templates: tools for the coverage certificates (T-cover) |
| `Hardness/Sec5/Templates/Inv.lean` | 342 | Section 5: the inversion template `x_a · x_b = 1` — template facts |
| `Hardness/Sec5/Templates/InvCover.lean` | 217 | Section 5: the inversion template — coverage by the canonical guards (T-cover) |
| `Hardness/Sec5/Templates/InvCoverData.lean` | 1190 | Section 5: the inversion template — T-cover certificates (generated) |
| `Hardness/Sec5/Templates/InvData.lean` | 1011 | Section 5: the inversion template — generated data |
| `Hardness/Sec5/Templates/InvMech.lean` | 520 | Section 5: the inversion template — the mechanism (paper Lemmas 49/50) |
| `Hardness/Sec5/Templates/Orient.lean` | 542 | Section 5: the orientation template `Add orient` (`u_A + u_B ≥ 5/2`) — template facts |
| `Hardness/Sec5/Templates/OrientCert.lean` | 995 | Section 5: the orientation template `Add orient` (`u_A + u_B ≥ 5/2`) — generated certificates |
| `Hardness/Sec5/Templates/OrientCover.lean` | 200 | Section 5: the orientation template — coverage by the canonical guards (T-cover) |
| `Hardness/Sec5/Templates/OrientCoverCert.lean` | 655 | Section 5: T-cover certificates of `Orient` — visibility of the pieces (generated) |
| `Hardness/Sec5/Templates/OrientCoverData.lean` | 862 | Section 5: the orientation template — T-cover certificates (generated) |
| `Hardness/Sec5/Templates/OrientData.lean` | 1106 | Section 5: the orientation template `Add orient` (`u_A + u_B ≥ 5/2`) — generated data |
| `Hardness/Sec5/Templates/Tools.lean` | 1315 | Section 5 templates: certificate tools for template chains |
| `Hardness/Correspondence.lean` | 42 | Theorem 54 (interface) |

Dependency graph (→ = "is used by"):
```
Vis.API ─→ Cones ─→ StationaryGuard ─┐
        ├→ Rooms ───────────────────┤
        ├→ Pinning ─────────────────┤
Geometry/Jordan → CertChecker ─→ Templates/{Inv,AddGE,AddLE,Orient} ─┐
Params → MainArea ──────────────────────────────────────────────────┤
Params → Corridor/Defs → Slabs → Shape → Visibility → Cover          │
                      └→ Copy ────────────────────────────┐          │
Corridor/* + Templates/* → Assemble (units, mirror) → Count → Constraint → Main
                                                └──────→ Cover ──────────┘
```
## 3. Definitions (Lean shapes)

* `Sec5.N (n k) := max (4n+k) 2`, `S := 200000 * N^2 : ℕ`, `ρ := 3/(2S) : ℚ`, `δ := 9ρ`,
  `ε := 1/(8S)`.
* `slotX σ := 27σ/2`, `segment σ := [(slotX σ, 0), (slotX σ + 3/2, 0)]`.
* `pocket (one : Bool) (σ) : List (ℚ×ℚ)` (02), `bottomWall`, hexagon corners.
* `unitSpecs Φ n : List UnitSpec × List UnitSpec` with
  `UnitSpec := {kind : Kind, real : List ℕ, work : List ℕ}` (06 table).
* `corridor (H : ℚ) (work : List ℕ) (T : List (ℚ×ℚ)) : Corridor` record of named points
  (04), with `chainBefore`, `chainAfter`.
* `template : Kind → Template` (fixed lists).
* `unitChain`, `construct Φ n := bottomWall ++ [w_r, v_r] ++ rightUnits ++ [t_r, t_l] ++ leftUnits ++ [v_l]`.
* `guardCount := 46n + 16 k_add + 5 k_inv`, `canonicalGuards x : Finset Point`.
All definitions are structurally recursive over the constraint list / `List.range`.

## 4. Simplicity (i)

**Lemma S1 (chain decomposition).** `construct Φ n` is the concatenation of chains
`C_0 … C_r` (pockets, unit chains, hexagon corners) where consecutive chains share one endpoint
and each chain lies in a closed box `B_j`; boxes of non-consecutive chains are disjoint, and
consecutive boxes meet only in the shared endpoint.  *Proof:* explicit boxes:
pocket σ: `[27σ/2 − 6, 27σ/2 + 15/2] × [−6, 1]`; right unit m:
`[S, S+3+10^{-3}] × [H_m − 6/5, H_m + 3/2]`; left units mirrored; the six hexagon edges are
checked against these boxes by one-line inequalities (`H_m ≥ S+1`, `H_m + 3/2 ≤ S + 3N`).

**Lemma S2 (simple concatenation).** If chains are simple, pairwise disjoint except shared
endpoints, and the closing edge meets only its neighbours, the polygon is `Simple` (pure
combinatorics on `edge i ∩ edge j`, plus distinct vertices).

**Lemma S3 (pocket simple).** Fixed list (13–19 vertices) translated by `a_σ`: `decide` via
`CertChecker.simpleCheck` after translation invariance (`Simple` is invariant under
translations and positive scalings).

**Lemma S4 (unit simple).** (a) template part: fixed list ⇒ certificate; translation+scaling
invariance; (b) channel walls `c1 → first template vertex` and `last template vertex → d1`
(two long edges) are disjoint from everything else in the unit by sign conditions using
`S ≥ 800000`; (c) the corridor chain (`Corridor/Shape`): all vertices are listed with their
`(ζ, ξ)`-coordinates in closed form; consecutive edges are monotone in `X` along the upper wall
(`d1 → … → d0` is `X`-decreasing except vertical edges), the floor is on `y = H`; so the upper
wall is the graph of a function over `X` (with vertical steps) lying strictly above `y = H`
except at `c0, c1`; Lemma: an `X`-monotone chain is simple; floor and upper wall are separated by
`Y ≥ −1 + ρ/2` (all upper-wall vertices other than `d0, d1` have `Y ≥ −2ε`... see `Shape`).

## 5. Lower bound and pinning (ii), (iii)

**Positions.** `Pos := base σ (4n) ∪ corridorSG (u, k) ∪ receiver (u, τ) ∪ weakCopy u ∪ gadgetSG (u, j)`.
`|Pos| = g`.  For each position `X`: a witness `m_X` and a finite witness set `W_X ∋ m_X` with
* (W1) `Spot_X := {p ∈ filled | ∀ w ∈ W_X, Sees p w}` equals the segment / point `X`;
* (W2) the sets `V(m_X)` are pairwise disjoint (`V(w) := {p ∈ filled | Sees w p}`);
* (W3) for `X ≠ Y` no point *of the position* `Y` sees any `w ∈ W_X`.

| position | `m_X` | `W_X` | proof of (W1) | where `V(m_X)` lives |
|---|---|---|---|---|
| base σ | `t1` | `t0,t1,u0,u1` (+`q1,q2` if `one`) | 02 guard-segment lemma | pocket room σ (cone ∩ door = ∅) |
| corridor SG `p_k` | slot `q_b` (slope 4) | `q_a, q_b` | SG lemma (04) | thin cone along the slope-4 line below `p_k` |
| receiver / weak copy with pocket | `t1` | `t0,t1,u0,u1` | as base, with tilted shaft (u-cones aimed at a wall) | its pocket room |
| enclosed receiver `r_j` (Add templates) | far witness `Tu0` | `T0,T1,Tu0,Tu1` | cones bounded by `y = 0` (both sides) and by `x+y = s_j`, `x+y = s_j+3/2` | thin cone along `x+y = s_j` |
| gadget SG | slot `q_b` | `q_a, q_b` | SG lemma | thin cone |

**Lemma C1 (lower bound).** Pinning lemma part 1 with `M = {m_X}` (W2): `|G| ≥ g`.
(W2) is proved by box separation between units and pockets, and inside a unit by the explicit
cones (all `m_X` cones of a unit are pairwise disjoint thin wedges: corridor slope-4 lines are
parallel; template ones by certificate).

**Lemma C2 (exact count ⇒ pinned).** If `|G| = g` then for every position `X` exactly one guard
`g_X ∈ G` sees `m_X`, `g_X ≠ g_Y` for `X ≠ Y`, and every guard is some `g_X`.  Then, in the order
(1) base segments, (2) corridor SGs from left to right, (3) pocketed receivers and weak copies,
(4) gadget SGs, (5) enclosed receivers: each `w ∈ W_X` is seen by some guard; that guard is `g_Y`
for some `Y`; if `Y ≠ X` then `g_Y` is already pinned to position `Y` (earlier in the order) or
lies in `V(m_Y)` (later in the order), and both are excluded by (W3) resp. the cone facts
`V(m_Y) ∩ V(w) = ∅` for `Y` later than `X`.  Hence `g_X` sees all of `W_X`, so `g_X ∈ Spot_X = X`.
(The order is needed because the far witnesses of enclosed receivers and the long slope-2 slots of
corridor SGs cross other positions' cones; only already-pinned positions are compared with them.)

## 6. Corridor inequalities (Slabs)

Notation: `x_p ∈ [0, 14N]` abscissa of a base guard, `H ∈ [S+1, S+3N]`, local frame at
`O_c = (S+1, H+1)`, `ζ = Y − X`, `ξ = Y + X`.

* **(SL1)** ζ-offset of the line `p c0` on `X = 0`: `ζ_p = H/(S − x_p) − 1`, and
  `|ζ_p − ((H − S)/S + x_p/S)| ≤ x_p(H − S + x_p)/(S(S − x_p)) ≤ 17·14 N²/(S(S−14N)) < ε/40`.
  (`nlinarith` after clearing denominators: `40·238 N² < S − 14N` for `C = 200000`.)
* **(SL2)** for `|X| ≤ 38Nρ`, the line deviates from its `X = 0` value by at most
  `|slope − 1|·|X| ≤ (17N/S)·(57N/S) < ε/40`.
* **(SL3)** same for `p d0` with `+2ρ·(1 + 1/(S − x_p))` (`< ε/20` error), and for receivers:
  receiver point `m + (T + (t,0))/S`, line through `c1`/`d1`: ξ-offset
  `−(T.x + t + T.y)/(S + T.x + t) ` vs centre `ξ_ref + τδ + γρ`, error `≤ 100²/S² < ε/40`
  using `|T| ≤ 50`.
* **(SL4)** band separation: `Z(σ,3) + ε < Z(σ+1,0) − ε` (`δ − 3ρ = 6ρ > 2ε`), same for `Ξ`.
These replace the paper's Lemmas 32/33/39/40 (which carry the same content with a coarser
`ε/4`-bookkeeping); all are single rational inequalities in `N` (and `σ ≤ 4n ≤ 4N`).

**Corridor shape facts** (Shape): in `(ζ, ξ)` (units of `ε`), with `Lw_σ = Z(σ,2) − 2ε`,
`Rw_τ = Ξ(τ,2) − 2ε`: apex `u_σ = (Lw_σ, Rw_τ)`, valley `v = (Lw_prev, Rw_τ + ε/2)`, mouth corners
`z0 = (Lw, Rw − 2h)`, `z1 = (Lw − 2h, Rw)` with `h = 3ε` (so the mouth has width `6ε` and lies
in `[Z(σ,1)+4ε, Z(σ,2)] × [Ξ(τ,1)+4ε, Ξ(τ,2)]`, inside every band of the pair), umbra axis
through the crossing points of the extreme lines (exact formula from `Copy`), its height above the
valley `≥ 3ρ − O(ε)`; stationary guard `p = (base.x, A(base.x))`; `z'` on the axis at
`ξ ∈ [Rw + ε/16, Rw + 5ε/16]` (abscissa rounded up plus one grid unit `ε/8`).
**Receiver conditions** (Receiver.lean): `det(q_τ(t), z', z1) ≥ 0`, `det(q_τ(t), v, z1) ≥ 0`,
`det(q_τ(t), v, z') ≥ 0` for `t ∈ [0, 3/2]` (04 §Receiver conditions).

**Lemma V1 (bands).** A base guard on slot σ sees no point of the corridor outside
`{ζ ∈ [Z(σ,0)−ε, Z(σ,3)+ε]}` (T1 against the main-area wall below `c0` or above `d0`, or against
the corridor upper wall).  Receivers: same with `ξ`.
**Lemma V2 (critical sets).** The umbra critical set `U_σ` (points within `ε/100` above the axis
segment `[f0,f1]`) and the nook top edge `[n0, n1]` are seen, among all *positions*, only by
`s_σ`, `r_τ(σ)` (V1+SL4), not by corridor SGs (wedge below their own axis, and `A_σ ≥ A_σ'`
for pairs to the left / the valley blocks pairs to the right), not by gadget positions (the window
`c1d1` is crossed only along receiver strips, and other gadget positions are hidden behind the
upper channel wall — template certificate), not by base guards of other slots (V1).
**Lemma V3 (copy).** (Copy.lean, exact algebra) For `p ∈ s_σ`, `q ∈ r_τ`: `U_σ ⊆ V(p) ∪ V(q)`
iff `value(q) ≥ value(p)`; `[n0,n1] ⊆ V(p) ∪ V(q)` iff `value(q) ≤ value(p)`.
*Proof.* Perspective-axis computation (Lemma 27 generalised): the crossing point of `p c0` and
`q c1` is on `A_σ` iff the values agree, above iff `value(q) < value(p)`; the uncovered part
of `U_σ` is the wedge below the crossing.  Nook: projections through `z0, z1` onto `A'_σ`
coincide iff values agree, are in the wrong order iff `value(q) > value(p)`.  Both are identities
of rational functions in `t_p, t_q` (polynomial identity after clearing denominators).

## 7. Gadget lemmas (v) — template certificates

For each template `T` (fixed rational data) the following *template facts* are proved by
certified computation (`Vis/CertChecker`) on the template polygon `P_T` := template chain closed by
a fixed "stub" in place of the channel (the channel is handled in `Unit.lean`, §8):
* (T-simple) the chain is simple;
* (T-cones) list of witnesses with their cones (convex vertex, two generators);
* (T-W1) for every position: `Spot_X = X` (finitely many crossing certificates: for every point
  of a convex region outside `X` that is in all cones, some witness segment crosses an explicit
  edge — certificate = list of (region, witness, edge) with vertex-sign checks);
* (T-W2/W3) pairwise disjointness of the `m_X` cones; positions do not see foreign witnesses
  (crossing certificates);
* (T-mech) the mechanism lemma, as a statement about guard positions with real parameters:
  - `Add ge`: with guards `a' = r'_i(u_A)`, `b = r_j(u_B)`, `c = r_l(u_C)`:
    `Γ ⊆ V(a') ∪ V(b) ∪ V(c)` iff `u_C ≤ u_A + u_B`;
    proof = paper Lemma 41 (identity `χ = u_A + u_B` for the projection of the crossing point
    through `e_l`, verified symbolically: two lines through `e_A=(10,21/2)`, `e_B=(−10,21/2)`,
    projection through `e_C=(0,21/2)` to `y = −21/2`), plus visibility facts "`a'` sees
    `γ ∈ Γ` iff `γ` on/right of line `a' e_i`" etc. (cone of the corner `e_i` + crossing
    certificates against the pillar / channel wall);
  - `Add le`: same with `u_C + 5/2`; `Add orient`: `5/2 ≤ u_A + u_B` (stationary guard `p` at the
    value-`5/2` point of the removed `r_l`, wall `x = 0` below `e_l`);
  - weak copy (all Add variants): nook `(r_i, r'_i)` covered iff `u'_A ≤ u_A`;
  - `Inv`: umbra `(ξ0, ξ1)` covered iff `x_a x_b ≤ 1`, nook `(ξ2, ξ3)` covered iff `x_a x_b ≥ 1`
    (identities in the paper's Lemmas 49/50 — with the corrected `f2`);
* (T-cover) for parameter boxes of guard positions, the template room minus `Γ`/critical sets is
  covered (convex decomposition, see §9).
Certificates (see `10_template_certificates.md`) are checked by `decide` on ℤ-scaled data.  Statements with
real parameters (`u_A ∈ [1/2,2]` etc.) are reduced to vertex checks by convexity (the set of
segments from a convex set `P1` to a convex set `Q1` crosses a line `L` inside the edge iff the
four extreme crossings do: `L ∩ conv(P1 ∪ Q1)` is an interval with endpoints among crossings of
vertex pairs).

## 8. Units, scaling, mirror

**Lemma U1 (similarity).** For `φ(z) = m + z/S` (resp. `mirror ∘ φ`), all template facts transfer:
`det` scales by `1/S²` (sign preserved; mirror flips sign and orientation — handled by reversing the
chain), so crossing certificates and convexity transfer verbatim.  Only *local* statements are
transferred (segments contained in the unit box), and the global polygon is related to the
template polygon by: `filled ∩ B_u = φ(filled_T ∩ B_T)` where `B_u` is the unit box minus a
neighbourhood of the window — proved from (i) and the room lemma (both regions are rooms with the
same chain and door `c0 d0` resp. the stub).
**Lemma U2 (channel).** The two channel walls `c1 → φ(first)` and `φ(last) → d1` and the window
`c1 d1`: every receiver strip passes the window (SL3), every non-receiver position of the unit is
hidden from the window (crossing certificate against the upper channel wall `φ(e_j) → d1`, which
in template coordinates is the line through `e_j` and `(−S, S+3/2)`; the certificate is
parametric in `S` but only needs `S ≥ 10^5`).
**Lemma U3 (mirror).** `mirror` is an isometry; `Sees`, `filled`, `IsGuardSet` commute with it;
it maps the right-frame unit with working slots to the left unit; values transform by
`u = 5/2 − x`; hence (06) left orientation/≤-add units enforce `x(s_{gn+i}) ≤ x(s_{3n+i})`,
`x_a + x_b ≤ x_c`.

## 9. Sufficiency (vi) — coverage by canonical guards

Decompose `filled` into convex pieces with an assigned guard (or a short list of guards) such that
`conv({guard} ∪ piece) ⊆ filled` (T2):
* main hexagon: columns `[27σ/2 − 6, 27σ/2 + 15/2] × [1, S+3N]` ∩ hexagon → guard of slot σ
  (the segment crosses `y = 1` inside the door); side triangles → slots `0`, `4n−1` (02);
* pocket room σ: pieces `T0 ∪ chamber` (convex), shaft, roof spike, floor spike, `one`-spikes →
  guard of σ;
* corridor: (a) below the axes: pieces between consecutive vertical lines through
  `p_1, p_2, p_3` → `p_k` sees the part left of `x = p_k.x` below `A_k` (wedge `[180°,270°]`);
  (b) above the axes inside the bands: by V3 the crossing point `X_σ` is on `A_σ`, so the part of
  the cell of pair σ above `A_σ` is the union of `{ζ ≥ λ_{c0}(p)}` (seen by `p`) and
  `{ξ ≥ μ_{c1}(q)}` (seen by `q`) — each is a convex region bounded by lines through `c0`/`c1`
  and corridor walls; (c) nooks: mouth region + nook pocket, split at the common projection point;
  (d) floor slots: seen by their stationary guard (directions strictly inside its wedge);
* gadgets: template certificate (T-cover) — pieces with guard lists, for value boxes; Γ split along
  the three lines through the guards (exactly covered iff the inequality holds).

## 10. Main theorem assembly (vii)

* `Simple`: §4.  `g ≤ |G|`: C1.
* `|G| = g` ⇒ pinned (C2) ⇒ values `v_σ` on base slots, copies equal (V3 both directions, using
  that the pair's critical sets are seen only by the pair — V2), gadget constraints (T-mech) ⇒
  orientation units give `v(s_{gn+i}) = v(s_{3n+i})` (≥ right, ≤ left) ⇒ one value `x_i` per
  variable, `x_i ∈ [1/2, 2]`, add/inv constraints hold, `one` spikes give `x_i = 1`; and
  `(x_i + d_i, 0) = g_{base i} ∈ G`.  This gives both the "moreover" conjunct and (with the fixed
  statement) the `⇐` direction (the range hypothesis puts `(x_i + d_i, 0)` on `s_i`).
* `⇒`: canonical guards (06) are `g` pairwise distinct points (distinct positions are disjoint),
  contain `(x_i + d_i, 0)`, and form a guard set (§9).

## 11. Notes

1. **Statement of Theorem 54**: corrected as in §0.
2. **Template certificates**: the template facts are checked by `decide +kernel` on integer
   data (about 100 vertices per template).  To keep the numbers small, the slot corners of the
   templates are placed on a coarse grid (`07_template_vertices.md`, "Changes for the
   certificates"); see `10_template_certificates.md`.
3. **Coverage (vi)** is the largest part: the corridor part uses exact descriptions of the band
   regions (`Corridor/Cover*.lean`), the gadget parts are certificate-based (`Templates/*Cover*.lean`).
4. **Enclosed receiver `r_j`** (05 §Topology): its far witnesses cross other tubes; (W3) for it
   is proved against all positions (`Count*.lean`).
5. A common polynomial denominator is impossible (04 §Exactness).  Theorem 1 for integer
   coordinates is therefore derived from Stade's construction (`ArtGallery/Stade/`), which has
   one; the Section 5 construction is used for Theorems 54 and 55.
6. The paper's constants (C = 200000) are kept; all slab inequalities have large slack.

## 13. Corrections to the first version of the design

(These concern the design in these notes, not the paper.)
1. **V1** is false literally near the entrance `d0c0` (a base guard sees points with `ζ ≈ 0`);
   the band lemmas are proved in the window `|z.x − (S+1)| ≤ 57N/S`, which contains all
   critical sets.
2. **`A_σ ≥ A_σ'` for pairs to the left** fails by `O(1/S²)` for consecutive slots (by up to
   `2·10⁻⁴ ε` in examples). The stationary-guard exclusion is proved
   instead by: above `A_j` → cone of `p_j`; within `ε/4` of `A_j` → blocked by the upper-wall
   edge `z0_j → valley_{j+1}` (valley ≈ `37.6 ε` below `A_j`).
3. The exclusion holds only strictly above the axis (`p_k` sees its own axis), so the umbra
   statement needs `v₁ < v₀`.
4. `corridor ⊆ P` needs the extra global hypothesis `CorridorClear` (boundary points of `P` in
   the corridor polygon are on its boundary), supplied by `Assemble/Clear.lean`.
5. **Receiver view of the umbra / nook**: the receiver
   `q_τ` sees `U_σ` and the nook only along lines passing west of the reflex corner `z'` and below
   the valley `v`.  In the first design `v` and `z1` lay exactly on `ξ = Rw` and `z'` within
   `±ε/16` of it, while the lines of `q_τ` drift in `ξ` by `O(1/S)` per unit of `ζ`; the
   conditions failed in most configurations (and in real instances: points of the nook top edge
   and of `U_σ` next to the edge `z' z1` were unseen).  Fix: `v = (Lw_prev, Rw + ε/2)` and the
   abscissa of `z'` rounded up plus one grid unit (04 §Receiver conditions).
6. **Count (§5).** The enclosed receiver `r_j` is pinned with main witness `T0` (vertex 1), not
   `Tu0` (whose cone reaches the corridor through the window). Pinning order: corridor stationary
   guards west to east (necessary: a western slope-4 tip and an eastern slope-2 tip can be seen
   from one point), gadget SGs (`g`, then `p`), `r_j`, then pocketed receivers and the weak copy.
   Counting uses disjointness and zone containment of positions instead of "every point of a
   position sees its witness", so it does not need `SepAt`. Certificates: `CountTmpl*.lean`.
