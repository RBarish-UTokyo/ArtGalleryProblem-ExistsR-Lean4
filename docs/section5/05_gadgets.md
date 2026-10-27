# 05 — Gadget templates

A template lives in *template coordinates*; the real
point is `m + T/S` with `m = c1 + (1,−1)` (scale `1/S`, translation).  A template provides its
receiver segments `r_τ` (left endpoint, orientation), its other guard segments, its stationary
guards and the vertex chain from `c1` (excluded) to `d1` (excluded).
In template coordinates the corridor window is at `c1 = (−S, S)`, `d1 = (−S, S + 3/2)`, so all
lines from the gadget to the window are within `O(1/S)` of slope `−1`: receiver `r_τ` "looks"
through the window along its *strip* `{T : T.x + T.y ∈ [σ_τ, σ_τ + 3/2]}` (`σ_τ = T_τ.x + T_τ.y`).

All template coordinates are fixed rationals (independent of `n, k`), so every template fact can
be verified once by exact computation (08 §Template certificates).

## Gadget-segment pockets

`compact_pocket(a)`: the base pocket with mouth corners `a+(−2,1)`, `a+(4,1)` (same witnesses
`t0,t1,u0,u1`).  `tilted_pocket(a, d, L)`: same, but the shaft runs in direction `d` and has length
`L·|d|`; then the cones of `u0,u1` point in direction `−d` and can be aimed at a nearby wall so that
they stay local (needed so that witness cones of different positions do not meet, see the counting
argument in 03/T3).

## Inversion gadget `x_a · x_b = 1` (right side; slots `(a, 3n+b)`)

Paper §5.13 numbers, completed:

| object | template coordinates |
|---|---|
| `r_i` (τ=1, right-oriented, value = abscissa) | `[(1/2,0),(2,0)]`, compact pocket |
| `r_j` (τ=0, left-oriented, value = `15.9 − abscissa`) | `[(13.9,0.1),(15.4,0.1)]`, tilted pocket `d=(−1,−2)`, `L=12` (its `u`-cones must miss `g_s`); **left mouth corner `a + (−2, 3/5) = (11.9, 0.7)`** (was `a + (−2, 1)`, see below) |
| umbra shadow corners (floor) | `ξ0 = (7, 541/184)`, `ξ1 = (9, 259139/112792)` |
| umbra critical segment | `f0 = (499811/70923, 38731813/13049832)`, `f1 = (112379/15432, 4355591/1419744)` |
| nook shadow corners (ceiling) | `ξ2 = (7, 8865/752)`, `ξ3 = (9, 4214815/460976)` |
| nook critical segment | `f2 = (182083/25835, 231222249/19427920)` (as printed in the JACM version), `f3 = (205139/28156, 130288905/10586656)` |
| nook top edge | `nR = A'(15/2)`, `nL = A'(351/50)` on the line `f2 f3` (covers `[f2,f3]`) |
| stationary guard `g_s` | `A(16)` on the umbra line `A = f0f1` (convex vertex) |
| `z'` | `A(25/2)` |
| witness slots of `g_s` | floor slot on `ξ0ξ1` at the line through `g_s` with direction `(7,4)`; floor slot right of `ξ1` at the line through `g_s` with direction `(1,1)` (cones on opposite sides, crossing exactly at `g_s`); tips `g_s + s d` with `s` on the grid `1/400`, floor corners at most `1/200` below the floor line (certificates, 08 §11.2) |

Chain: `pocket(r_i), ξ0, slot_a, ξ1, slot_b, pocket(r_j), g_s, z', ξ3, nR, nL, ξ2`
(`g_s` has wedge `[203°, 288.5°]`; its two slots at directions `210°`, `225°` lie strictly inside).
(then the upper channel wall to `d1`).

Mechanism (paper Lemmas 49–51, re-verified exactly): for guards `p=(x,0)` on `r_i`,
`q=(15.9−y, 0.1)` on `r_j`: the lines `pξ0`, `qξ1` meet on the line `f0f1` iff `xy = 1`; if `xy > 1`
the crossing is above `f0f1` and points just above `f0f1` below the crossing are unseen; the
projections of `p` through `ξ2` and of `q` through `ξ3` onto `f2f3` coincide iff `xy = 1` and are in
the wrong order iff `xy < 1`.

**Left mouth corner of the `r_j` pocket.**  The corner is `(11.9, 0.7)`, with margin `0.3` below
the line from `q = (13.9, 0.1)` (value `y = 2`) through `ξ1`.  A corner `a + (−2, 1) = (11.9, 1.1)`
would lie above this line: for `y ∈ (1.58, 2]` the guard of `r_j` would not see past `ξ1` (blocked
by the floor `ξ1 → (11.9, 1.1)`), so for `x y = 1`, e.g. `x = 1/2`, `y = 2`, the points just above
the crossing `X(1/2, 2)` (above the axis) would be seen by no guard.  The certificates
(`ArtGallery/Hardness/Sec5/Templates/Inv*.lean`) are for this template.

## Topological constraint for three-input gadgets (new; not in the paper)

The union of the visibility tubes of a gadget is in the interior; since `filled` is simply
connected, any cycle of tubes encloses only interior points.  In an addition gadget three guard
families see the same region `Γ` and each is connected (through its receiver strip, possibly via a
nook) to the window `c1d1`.  The three "window–Γ paths" form a theta graph; the *middle* path lies
between two interior faces and therefore cannot carry a pocket or a nook.  Consequently one
receiver of every addition gadget needs **far witnesses**: spikes on the outer boundary whose thin
cones cross the other tubes and meet exactly in that receiver (two cones bounded by its line
`y = const` from opposite sides, two cones bounded by the lines `x+y = const` through its endpoints,
which never cross other receivers' strips).  In the paper's layout this is `r_j`; the paper handles it only in
its figures (Figs. 22–24: a spike below `c1` and a pillar-wall slot at the height of `r_j`, a notch
on the lower corridor wall), without describing it in the text (`docs/paper_issues.md`, A3).

## Addition-type templates `Add(variant)` — `ge`, `le`, `orient`

Mechanism of the paper (Lemma 41) with `v = 10`, `h = 21/2`: corners `e_j = (−10, 21/2)` (end of
the upper channel wall), `e_l = (0, 21/2)`, `e_i = (10, 21/2)` (top of the *pillar*, an exterior
block between `r_l` and `r'_i`).  For guards `A ∈ r'_i`, `B ∈ r_j` at height 0 and `C` at height
`−21/2`, the lines `A e_i`, `B e_j` meet in `γ`, and the projection of `γ` through `e_l` to
`y = −21/2` has abscissa `A.x + B.x` (identity, any positions); `Γ` (the quadrilateral of all such
`γ`, ≈ `(0, 17.4)`) is covered iff `C.x ≤ A.x + B.x`.

| point | `ge` | `le` (= mirror of the paper's ≤-gadget) | `orient` |
|---|---|---|---|
| `r_i` (τ=2 / τ=1 in orient; summand, weakly copied) | `(−22,−35/2)` | `(−22,−15)` | `(−22,−35/2)` |
| `r_j` (τ=1 / τ=0; summand `B`, *enclosed*) | `(−26,0)` | `(−47/2,0)` | `(−26,0)` |
| `r_l` (τ=0; sum `C`) | `(−2,−21/2)` | `(1/2,−21/2)` | — (stationary guard `p=(0,−21/2)`, value 5/2) |
| `r'_i` (weak copy, `A`) | `(49/2,0)` | `(22,0)` | `(49/2,0)` |
| `z` (blocks `r_i` from `Γ`) | `(−25/2,−3/2)` | `(−13,−2/5)` (not `(−25/2,−1/10)`, see below) | `(−25/2,−3/2)` |
| nook `Q_i` shadow corners | `(5/2,34)`, `(9/2,34)` | same | same |
(all segments right-oriented in the working frame; left endpoints listed.)

Structure of the chain: far-witness spike `T0` of `r_j` on the lower
channel wall at `y = 0` (cone above `y = 0`); tilted pocket of `r_i` (shaft `d = (−2,−3)`, its
`u`-cones aimed at the z-block); left edge of the *z-block* carrying the far-witness spikes `Tu0`,
`Tu1` of `r_j` on the lines `x+y = s_j`, `x+y = s_j+3/2` (cones pointing up-left along `r_j`'s
own strip); `z`; right edge of the z-block (in `orient`: two witness slots of `p` and the corner
`p`); tilted pocket of `r_l` (shaft `(−1,−2)`, `u`-cones aimed at the pillar); pillar left wall
with the far-witness spike `T1` of `r_j` (cone below `y = 0`; in `orient` the wall is `x = 0`);
`e_l`; two witness slots of the stationary guard `g` in the pillar top (directions `≈ 334°`,
`≈ 342°` from `g`); `e_i`; pillar right wall; tilted pocket of `r'_i`; right wall to `(·, 34)`;
nook `k1, n1, n0, k0` (top edge on the exact copy axis of `(r_i, r'_i)`); `TL = (−4,34)`;
`z_g = (−7, 16 − 3/8)`; stationary guard `g = (−10, 16)` (convex corner; it sees exactly the region
below the line `y = 16 − (x+10)/8` and right of `x = −10`, which contains the only region not seen
by the segment guards — the triangle above the pillar top between `e_l` and `e_i` — and misses `Γ`
and the nook); `e_j`; then the upper channel wall to `d1`.

**`le`: the corner `z`.**  With `z = (−25/2, −1/10)` the guard of `r_i` with value `1/2`
would see the corner of `Γ` where `u_A + u_B ≥ 3.5` (sight lines pass just above `z`); the guards of
`r_i` must not see `Γ` (only `a'`, `b`, `c` may, otherwise the constraint is not enforced in
general position).  `z = (−13, −2/5)` separates the sight lines of `r_i` to `Γ` (blocked by the
z-block) from those to the weak-copy nook (passing above `z`) and stays below `y = 0` (the far
witness `T1` of `r_j` is seen along `y = 0`); certified in `Templates/AddLE*.lean`.
