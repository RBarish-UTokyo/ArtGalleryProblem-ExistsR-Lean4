# Stade's reduction ETR-INV-REV → point-boundary AGP: explicit construction

Source: J. Stade, *The Point-Boundary Art Gallery Problem Is ∃ℝ-Hard*, SoCG 2025, full version
arXiv:2210.12817v3 (cited as [S]).  Proof structure: `docs/stade/proof_plan.md`.

This document fixes **every vertex** of the polygon `P(Φ)` as an explicit formula in the instance
data, the guard number `g(Φ)`, the canonical guard set built from a solution, and the affine
correspondence between guards and variables.  It deviates from [S] wherever this makes the
formal verification simpler; all deviations are listed in §10.

Instances are lists of `ArtGallery.ETRINVREV.Constraint` (file `ArtGallery/ETR/REVDefs.lean`):

| constraint        | meaning (Spec)            | gadget           |
|-------------------|---------------------------|------------------|
| `one x`           | `v x = 1`                 | two extra wedges on the variable segment |
| `invGe x y`       | `1 ≤ v x * v y`           | `invGe` pocket (§6.1)    |
| `invRevLe x y`    | `v x * (5/2 − v y) ≤ 1`   | `invRevLe` pocket (§6.2) |
| `addLe x y z`     | `v x + v y ≤ v z`         | `addLe` room (§7.1)      |
| `addGe x y z`     | `v z ≤ v x + v y`         | `addGe` room (§7.2)      |

All variables used must be `< n`.  Repeated variables (`invGe x x`, `addLe x x x`, …) need no special
treatment: every occurrence gets its own input segment and its own copy nook.

---------------------------------------------------------------------------------------------------

## 1. Overview

* A huge axis-parallel rectangle, the **hall** `𝓗 = [x_L, x_R] × [−1, 2H]`, is the convex core of the
  polygon.  Everything else is a **feature** glued to the floor `y = −1` (below it) or to the
  ceiling `y = 2H` (above it) through an **opening** that is a subsegment of the floor/ceiling.
  The hall itself has no internal walls, so all sight lines inside it are free.
* Guard regions (§2):
  * **variable segment** `σ_k = {a_k} × [H, H+3]`, `k < n`; value `v ↦ (a_k, H + 2v − 1)`;
  * **input segment** `τ_j = {b_j} × [0, 6]` (one per occurrence of a variable in a constraint
    other than `one`); value `v ↦ (b_j, 4v − 2)`;
  * **aux region** `A_c` (one per addition constraint), a convex polygon inside the gadget room.
  Each segment region is cut out by 3 thin wedges (5 for a variable with a `one` constraint) whose
  visibility cones lie in the vertical **slab** `|x − s| ≤ 3` of the segment (`s` its abscissa);
  each aux region is the visibility cone of one wedge intersected with its room.
* **Copy nooks** (§5) hang above the ceiling at `x ≈ 2a_k − b_j < 0`; each relates `σ_k` and `τ_j`
  by `v_var ≥ v_in` (type GE) or `v_var ≤ v_in` (type LE).
* **Constraint gadgets** hang below the floor in slots of width `W_S = 1200` to the right of the
  variables, one slot per non-`one` constraint.

Guard number: `g(Φ) = n + m + A` where `m` = number of input segments (2 per inversion, 3 per
addition constraint) and `A` = number of addition constraints.

## 2. Global parameters

Let `Φ` be the instance, `gad = [c ∈ Φ | c is not 'one']` (order of `Φ` kept), `C = |gad|`,
`ones = {x | one x ∈ Φ}`.

```
W_S = 1200                       slot width
D_V = 600·C + 50                 spacing of variable segments
H   = max(1000, (n−1)·D_V + 1200·C)
X_0 = H + (n−1)·D_V              left end of the gadget row
a_k = k·D_V                      (k < n)          variable abscissae
g_c = X_0 + c·W_S                (c < C)          origin of slot c
x_L = −3H,   x_R = X_0 + C·W_S + 100
```

Consequences used throughout (all checked in Lean by `omega`/`nlinarith`):
* every input abscissa `b` and variable abscissa `a` satisfy `H ≤ b − a ≤ 2H`
  (`b − a ≥ X_0 − (n−1)D_V = H`, `b − a ≤ X_0 + C·W_S = 2H` when `H = (n−1)D_V + 1200C`, and
  `≤ 2H` trivially otherwise); this is the slope window `1/2 ≤ H/(b−a) ≤ 1` of [S] §4.2;
* distinct regions have abscissae at distance `> 20` (variables `D_V ≥ 650` apart, inputs `≥ 60`
  apart (templates), inputs `≥ H` to the right of the variables);
* coordinates are bounded by `4H` in absolute value except for the needles below the floor, which
  go down to `−H − 200`; `H = O((n+1)·|Φ|)`.

Value maps (fixed once and for all):
```
variable k :  v ↦ (a_k, H + 2v − 1)      v ∈ [1/2, 2]  ↦  y ∈ [H, H+3]
input    j :  v ↦ (b_j, 4v − 2)          v ∈ [1/2, 2]  ↦  y ∈ [0, 6]
```
(The length ratio 3 : 6 and the centres `H + 3/2`, `3` make the two openings of every copy nook
fall on the ceiling `y = 2H`; see §5.)

## 3. Boundary order

The vertex list is (counterclockwise; the interior is to the left of every edge):

```
(x_L, −1),
  FLOOR FEATURES in increasing x  (each a chain starting/ending on y = −1, or below it),
(x_R, −1), (x_R, 2H),
  CEILING FEATURES in decreasing x (each a chain starting/ending on y = 2H, or above it),
(x_L, 2H)
```
Between consecutive features the boundary runs along the floor/ceiling line (one edge).
Orientation: the left wall `(x_L, 2H) → (x_L, −1)` is an *extreme* edge (every vertex has
`x ≥ x_L`, since all features lie in `x > −2H − 20 > −3H`), traversed downward; after the rotation
`(x, y) ↦ (−y, x)` it is a bottom edge traversed left to right, so `interiorLeft_of_bottom_edge`
(+ rotation invariance, `ArtGallery/Invariance/Affine.lean`) gives `InteriorLeft` (proof plan L2.1).

Floor features (left to right): the `W2` needles of the variables (§4), then for each slot
`c = 0..C−1` the gadget chain of `gad[c]` translated by `g_c` (§6, §7), which contains the
`W2` needles of its inputs.  Ceiling features (right to left): `W1`, `W3` (and `W4`, `W5`) needles of
the inputs and variables, sorted by decreasing `x`, then the copy nooks sorted by decreasing
`x` (they all lie at `x < 0` while all needles lie at `x ≥ 0`).

## 4. Wedges ("needles")

For a segment region at abscissa `s` with range `[y_lo, y_hi]` and **side** `σ ∈ {+1, −1}`
(given per region: variables `σ = +1`; inputs: see the templates):

| wedge | vertices (in boundary order)                                   | cone (viewers ⊆ cone) |
|-------|----------------------------------------------------------------|-----------------------|
| `W1` (top, primary) | mouth `(s,2H)`, `(s+σ/4,2H)`; tip `T1 = (s, 3H)`          | between the rays `T1→(s,2H)` (vertical) and `T1→(s+σ/4,2H)`: the side `σ` of the line `x = s` |
| `W2` (bottom) | mouth `(s,−1)`, `(s−σ/4,−1)`; tip `T2 = (s, −1−H)` (floor needle) | the side `−σ` of the line `x = s` |
| `W3` (cutter) | tip `T3 = (s − σ/2, T)`, `T = 3H` (variables) / `4H` (inputs); mouth = the two points of `y = 2H` on the rays `T3→(s,y_lo)`, `T3→(s,y_hi)`, i.e. `x = s − σ/4` and `x = s − σ(H−3)/(2(2H−3))` (same formulas for both kinds) | cone ∩ {x = s} = `{s} × [y_lo, y_hi]` |
| `W4`, `W5` (only for `k ∈ ones`) | tips `(s−3σ/4, 3H)`, `(s−σ, 3H)`; rays through `(s,H)`,`(s,H+1)` resp. `(s,H+1)`,`(s,H+3)`; mouth abscissae `s − 3σ/8`, `s − 3σ(H−1)/(4(2H−1))` resp. `s − σ(H−1)/(2H−1)`, `s − σ(H−3)/(2H−3)` | cone ∩ {x=s} = `[H,H+1]` resp. `[H+1,H+3]` |

Each wedge is a triangle (tip + mouth); in the boundary it appears as `mouth-end, tip, mouth-end`
(ceiling: right end first; floor: left end first).  Chain-attached `W2` needles (inputs above a
pocket or a room, §6.2, §7) have mouth `(s, β(s)), (s+1/4, β(s+1/4))` on a wall line `y = β(x)` and tip
`(s, β(s) − H)`, side `σ = −1`.

Facts (proof plan L4.x):
* `W1 ∩ W2 ∩ W3` cones meet in exactly the segment; with `W4, W5` in exactly `{(s, H+1)}`
  (value 1).
* Every cone, restricted to the horizontal strip `[y_min, y_max] ⊆ [−H−130, 4H]` of the polygon, lies in
  the slab `|x − s| ≤ 3`.  A cone with tip `(s+t, T)` and boundary rays of horizontal slopes `q₁, q₂`
  (per unit of descent) stays in `s + t + [min q·(T−y_min), max q·(T−y_min)]`; with the data above:
  `W1` ⊆ `[s, s+(4H+130)/(4H)]`, `W2` ⊆ `[s−(5H+130)/(4H), s]`, `W3` ⊆ `[s−1/2, s+0.65]` (σ = +1),
  `W4, W5` ⊆ `[s−1, s+1.1]`; all `< 3` for `H ≥ 1000`.  Slabs of distinct regions are disjoint (all
  segment abscissae differ by more than 6; exact clip check `check_slabs`).

## 5. Copy nooks

For input `j` at `b = b_j` copying variable `k` at `a = a_k` with type `t ∈ {GE, LE}`
(`GE`: enforce `v_k ≥ v_in`, `LE`: `v_k ≤ v_in`):

```
e      = +12 (GE),  −16 (LE)
x_N    = 2a − b + e
ℓ      = 6/(2H−3)                                 (nook length)
N_top  = (x_N, 2H + 1 + 3/(2H−3)),   N_bot = (x_N, 2H + 1 − 3/(2H−3))
P_σ    = ((x_N(2H−3) + 2a)/(2H−1), 2H)          homothety centre σ_k → N  (ratio −ℓ/3)
P_τ    = ((x_N(2H−3) + b)/(2H−2), 2H)           homothety centre τ_j → N  (ratio −ℓ/6)
```
`P_σ, P_τ` lie on the ceiling because `(2H − (H+3/2)) : (2H − 3) = 3 : 6` (centres and lengths of
`σ` and `τ`).  Let `R_m` = the one of `P_σ, P_τ` with larger abscissa (`P_τ` for GE, `P_σ` for LE),
`L_m` the other.  Boundary chain (ceiling, right to left): `R_m, N_top, N_bot, L_m`.
The pocket is the convex quadrilateral `N_bot, L_m, R_m, N_top` (walls `N_bot L_m`, `R_m N_top`),
the mouth is `[L_m, R_m]` on the ceiling.

Homothety facts: `σ_bot, P_σ, N_top` collinear and `σ_top, P_σ, N_bot` collinear; likewise for `τ`
and `P_τ`.  A guard at value `u` on `σ` projects through `P_σ` to height `N_top − (2ℓ/3)(u − 1/2)`
on the nook line; same formula for `τ` through `P_τ`.

Non-restriction conditions (GE; LE symmetric), equivalent to linear inequalities in `e`
(`Δ = b − a ∈ [H, 2H]`):
```
GE:  e(H+3) ≥ Δ(5 + ℓ/2)          (σ not restricted by P_τ, τ not restricted by P_σ)
LE: −e(H−6) ≥ Δ(7 + ℓ/2)
```
which hold for `e = 12`, resp. `e = −16`, since `Δ ≤ 2H` and `H ≥ 1000`.
Coverage: GE nook covered by the two guards iff `v_var ≥ v_in`; LE iff `v_var ≤ v_in`.

Partial-visibility region `PV` (proof plan L5.3) = beyond the mouth and between the diagonals
`N_top L_m`, `N_bot R_m` (GE: these pass through `σ_bot` and `τ_top`).  At the variable band it is
contained in `|x − a| ≤ 15`, at the input band in `[b − 27, b + 27]` (on test instances with `H` up to 14500
the largest values are 12.40 resp. 24.80), and it does not reach any aux region (proved in Lean).

Copy pockets are pairwise separated: `x_N(j) − x_N(j')` is at least `6` for `j ≠ j'` (same
variable: `|b_j − b_j'| − 28 ≥ 32`; different variables: `2D_V − 1200C − 28 > 0`), and every
pocket lies in `x_N ≤ x ≤ x_N + 3`.

## 6. Inversion gadgets (floor pockets with a corridor)

A gadget in slot `c` is given in **local coordinates** (`x_local = x − g_c`; floor `y = −1`,
inputs `{dx} × [0,6]`).  Both inversion gadgets realise a *perspectivity* between the two input
lines through a common nook line, designed with the classical criterion "a projectivity between
two lines is a perspectivity iff it fixes their intersection point" (this replaces [S, Lemmas
5.3–5.6] and needs no square roots).

### 6.1 `invGe x y` (`v_x v_y ≥ 1`)
x-input at local `40` (W1 side `+1`, floor needle on the left), y-input at `100` (side `−1`, floor
needle on the right).  Pocket `J = (61,−78)`, `I = (79,−78)` (nook segment), mouth corners
`P = (43,−6)` (restricts the x-guard), `Q = (97,−6)` (restricts the y-guard); corridor
`(81/2,−1), P, Q, (199/2,−1)` (walls along the lines `I P` and `J Q`, which pass through the
input bottoms `(40,0)` and `(100,0)`).  Floor chain:
`(81/2,−1), (43,−6), (61,−78), (79,−78), (97,−6), (199/2,−1)`.
Derivation: x-input at `0`, y-input at `w`, nook line `y = −m`; the projectivity
`v ↦ 1/v` between the input lines has the fixed heights `y = 2` (`v=1`) and `y = −6` (`v=−1`), so
the mouth can be the horizontal line `y = −6` (this is why the corridor goes down to `−6`);
then `P = (4w/(m+2), −6)`, `Q = (w(m−2)/(m+2), −6)`, `J = w(m+6)/(3(m+2))`, `I = 2wm/(3(m+2))`.
With `w = 60`, `m = 78`: arms of slope `±2` (steeper than all copy lines, slope ≤ 1).
Shadows (abscissa on the nook line): x-guard of value `v`: `40 + 3(v+19)/(v+1)`; y-guard:
`40 + 3(1+19v)/(1+v)`.  The x-guard sees `[shadow, I]`, the y-guard `[J, shadow]`; covered ⟺
`(v_x+19)(1+v_y) ≤ (1+19v_y)(v_x+1)` ⟺ `v_x v_y ≥ 1`.

### 6.2 `invRevLe x y` (`v_x (5/2 − v_y) ≤ 1`)
x-input at local `60` (side `−1`; its `W2` hangs from the pocket wall `I Q`), y-input at `104`
(side `−1`, floor needle on the right).  Opening `P = (59,−1)` lies **on the floor**, `Q = (80,−8)`,
nook `J = (38,−22)`, `I = (56,−22)`; corridor triangle `P, Q, Q' = (101,−1)` (`Q'` on the line
`J Q`).  The x-needle: base points `(60, −59/3)`, `(241/4, −937/48)` on the line `I Q`
(`β(x) = −22 + 7(x−56)/12`), tip `(60, −59/3 − H)`.  Floor chain:
`(59,−1), (38,−22), (56,−22), (60,−59/3), (60,−59/3−H), (241/4,−937/48), (80,−8), (101,−1)`.
The projectivity `v ↦ 5/2 − 1/v` fixes exactly the heights `0` and `6` of the input lines, so the
mouth cannot be horizontal below the floor (one corner must be within 2 units of the x-input's
bottom – this is why the floor is at `y = −1` and why the x-needle hangs from the pocket, cf. the
small spike in [S, Fig. 17]).  Shadows on `y = −22`: x-guard `60 − 4(5+v)/(4v−1)`, y-guard
`104 − 48(5+v)/(3+2v)`; the x-guard sees `[shadow, I]`, the y-guard `[J, shadow]`; covered ⟺
`v_x(5/2 − v_y) ≤ 1`.  The partial-visibility region goes **up-right** (away from all variables).

## 7. Addition gadgets (rooms below the floor)

Each addition gadget is a convex **room** hanging below the floor through a single window
`[WL, WR] × {−1}`, with three nook pockets on its left wall, the aux wedge hanging from its
bottom, and needles (`W2`) of the inputs that stand above the window hanging from its bottom.
(A single window is forced: several openings into one room would create holes.)

### 7.1 Algebraic core (both kinds)
Unshifted coordinates: nooks on `x = 0`, aux openings `P = (d, p)`, `Q = (d, q)`, `R = (d, r)`,
input openings `N1 = (d, n1)` (x), `N3 = (d, n3)` (y), `N2 = (d − δ, n2)` (z), inputs
`{b_i} × [0,6]`.  With `k_i = N_i.x/(b_i − N_i.x)` the input of value `v` projects through `N_i`
to `s_i(v) = n_i + k_i(n_i − (4v−2)) = c_i − 4k_i v`, `c_i = n_i(1+k_i) + 2k_i`.
Choose `μ = k_y/(k_x+k_y)`, `k_z = k_x k_y/(k_x+k_y)` (this determines `b_z`),
`q = μ p + (1−μ) r`, `c_z = μ c_x + (1−μ) c_y` (this determines `n2`).
**Identity** (replaces [S, Lemma 5.7] and its projective map): for every point `a` right of
`x = d`, `π_Q(a) = μ π_P(a) + (1−μ) π_R(a)` where `π_O(a)` is the projection of `a` through `O`
onto `x = 0` (`π_O(a) = s·O_y − (s−1)a_y`, `s = a_x/(a_x − d)`, affine in `O_y`).
* `addLe` (`x + y ≤ z`): the aux sees nook x above `π_P`, nook y above `π_R`, nook z below `π_Q`;
  inputs see the complements below `s_x`, below `s_y`, above `s_z`.  Covered ⇒
  `s_z(v_z) ≤ π_Q = μπ_P + (1−μ)π_R ≤ μ s_x(v_x) + (1−μ)s_y(v_y)` ⇒ `v_x + v_y ≤ v_z`.
* `addGe` (`v_z ≤ v_x + v_y`): all sides reversed.  A **sign obstruction** forces `δ > 0`: with all
  six openings on one vertical line, `n2 − q = μ(n1−p) + (1−μ)(n3−r) + k_z((1−μ)n1 + μn3 + 2)/(1+k_z)`,
  and for openings below the input level (`n < −2`) the last term is negative, which is compatible
  with `addLe` (needs `N2` below `Q`) but not with `addGe` (needs `N2` "above" `Q`).  Recessing
  `N2` to `x = d − δ` creates a small convex **bay** `N1, N2, Q` (cf. the zig-zag wall in
  [S, Fig. 30]).
* Nook segments: `[c_i − 8k_i, c_i − 2k_i]` (the shadow range) extended by `marg` on the side the
  aux must cover (needed for the "covered ⇒ inequality" step at the extreme values).
* Canonical aux point (for (b)): `I(v_x,v_y)` with `π_P(I) = s_x(v_x)`, `π_R(I) = s_y(v_y)`:
  `s = (s_x − s_y)/(p − r)`, `I = (s d/(s−1), (s p − s_x)/(s−1))`.
Then everything is translated by `+30` (nook line at local `x = 30`, openings at `x = 50`).

Parameters (chosen by an exact search maximising the exclusion margins):

| | `d` | `δ` | `b_x` | `b_y` | `b_z` | `p` | `r` | `n1` | `n3` | `marg` | `μ` | `k_x,k_y,k_z` |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| addLe | 20 | 0 | 340 | 180 | 500 | −113 | −128 | −445/4 | −491/4 | 1/16 | 2/3 | 1/16, 1/8, 1/24 |
| addGe | 20 | 35/2 | 340 | 180 | 125/2 | −37 | −77 | −153/4 | −94 | 3/8 | 2/3 | 1/16, 1/8, 1/24 |

### 7.2 Room, window, needles, aux wedge
* left wall `x = 50` through the six openings (top `T0`, bottom `B0`; for addGe with the bay);
* window `[WL, WR]` = the smallest integer interval (± 1) containing all crossings of the floor by
  the segments joining the inputs to the mouths of their pockets; upper-left wall `WL → T0`;
* bottom `y = B0_y`, right wall `x = WR`;
* inputs above the window (`WL < b < WR`) get their `W2` hanging from the bottom
  (`(b, B0_y), (b + 1/4, B0_y)`, tip `(b, B0_y − H)`), the others a floor needle on the far side;
* aux wedge below the bottom: mouth `(x_c ∓ w, B0_y)`, tip `(x_c, B0_y − h)` with `x_c` the rounded
  centre of the aux points, `w = 1/4`, `h` the largest multiple of `1/4` such that the cone
  contains all canonical aux points (the cone points up into the upper-left wall).
  `A_c := cone ∩ room` is the aux region.

### 7.3 Template tables (exact, local coordinates)
### template `invGe`
inputs (role, local x, side σ of W1, W2 attachment): (x, 40, +1, floor), (y, 100, -1, floor)
floor chain (left to right; `β − H` marks a needle tip at depth H below its base point):
`(81/2, -1), (43, -6), (61, -78), (79, -78), (97, -6), (199/2, -1)`
nook : segment (61, -78)–(79, -78), mouth (43, -6)–(97, -6), pocket [lo,dn,up,hi] = [(61, -78), (43, -6), (97, -6), (79, -78)], guards ['x', 'y']

### template `invRevLe`
inputs (role, local x, side σ of W1, W2 attachment): (x, 60, -1, chain), (y, 104, -1, floor)
floor chain (left to right; `β − H` marks a needle tip at depth H below its base point):
`(59, -1), (38, -22), (56, -22), (60, -59/3), (60, -59/3 − H), (241/4, -937/48), (80, -8), (101, -1)`
nook : segment (38, -22)–(56, -22), mouth (59, -1)–(80, -8), pocket [lo,dn,up,hi] = [(38, -22), (59, -1), (80, -8), (56, -22)], guards ['x', 'y']
wedge (x): tip (60, -59/3 − H), mouth (60, -59/3)–(241/4, -937/48)

### template `addLe`
inputs (role, local x, side σ of W1, W2 attachment): (x, 370, -1, chain), (y, 210, -1, chain), (z, 530, -1, floor)
floor chain (left to right; `β − H` marks a needle tip at depth H below its base point):
`(200, -1), (50, -445/4), (30, -7561/64), (30, -7589/64), (50, -113), (50, -118), (30, -499/4), (30, -2001/16), (50, -2994/25), (50, -491/4), (30, -4417/32), (30, -4443/32), (50, -128), (439/4, -128), (110, -519/4), (441/4, -128), (210, -128), (210, -128 − H), (841/4, -128), (370, -128), (370, -128 − H), (1481/4, -128), (527, -128), (527, -1)`
nook x: segment (30, -7589/64)–(30, -7561/64), mouth (50, -113)–(50, -445/4), pocket [lo,dn,up,hi] = [(30, -7589/64), (50, -113), (50, -445/4), (30, -7561/64)], guards ['x', 'aux']
nook y: segment (30, -4443/32)–(30, -4417/32), mouth (50, -128)–(50, -491/4), pocket [lo,dn,up,hi] = [(30, -4443/32), (50, -128), (50, -491/4), (30, -4417/32)], guards ['y', 'aux']
nook z: segment (30, -2001/16)–(30, -499/4), mouth (50, -2994/25)–(50, -118), pocket [lo,dn,up,hi] = [(30, -2001/16), (50, -2994/25), (50, -118), (30, -499/4)], guards ['z', 'aux']
wedge (y): tip (210, -128 − H), mouth (210, -128)–(841/4, -128)
wedge (x): tip (370, -128 − H), mouth (370, -128)–(1481/4, -128)
wedge (aux): tip (110, -519/4), mouth (439/4, -128)–(441/4, -128)
room (convex part) = [(200, -1), (50, -445/4), (50, -128), (527, -128), (527, -1)]
addgen parameters: μ = 2/3, k = {'x': '1/16', 'y': '1/8', 'z': '1/24'}, c = {'x': '-7557/64', 'y': '-4411/32', 'z': '-374/3'}, openings P=(20, -113) Q=(20, -118) R=(20, -128) N1=(20, -445/4) N2=(20, -2994/25) N3=(20, -491/4) (unshifted, nook line x=0)

### template `addGe`
inputs (role, local x, side σ of W1, W2 attachment): (x, 370, -1, floor), (y, 210, -1, chain), (z, 185/2, -1, chain)
floor chain (left to right; `β − H` marks a needle tip at depth H below its base point):
`(85, -1), (50, -37), (30, -2601/64), (30, -2649/64), (50, -153/4), (65/2, -5977/100), (30, -5941/96), (30, -6001/96), (50, -151/3), (50, -77), (30, -423/4), (30, -855/8), (50, -94), (327/4, -94), (82, -113), (329/4, -94), (185/2, -94), (185/2, -94 − H), (371/4, -94), (210, -94), (210, -94 − H), (841/4, -94), (363, -94), (363, -1)`
nook x: segment (30, -2649/64)–(30, -2601/64), mouth (50, -153/4)–(50, -37), pocket [lo,dn,up,hi] = [(30, -2649/64), (50, -153/4), (50, -37), (30, -2601/64)], guards ['x', 'aux']
nook y: segment (30, -855/8)–(30, -423/4), mouth (50, -94)–(50, -77), pocket [lo,dn,up,hi] = [(30, -855/8), (50, -94), (50, -77), (30, -423/4)], guards ['y', 'aux']
nook z: segment (30, -6001/96)–(30, -5941/96), mouth (50, -151/3)–(65/2, -5977/100), pocket [lo,dn,up,hi] = [(30, -6001/96), (50, -151/3), (65/2, -5977/100), (30, -5941/96)], guards ['z', 'aux']
wedge (z): tip (185/2, -94 − H), mouth (185/2, -94)–(371/4, -94)
wedge (y): tip (210, -94 − H), mouth (210, -94)–(841/4, -94)
wedge (aux): tip (82, -113), mouth (327/4, -94)–(329/4, -94)
room (convex part) = [(85, -1), (50, -37), (50, -94), (363, -94), (363, -1)]
addgen parameters: μ = 2/3, k = {'x': '1/16', 'y': '1/8', 'z': '1/24'}, c = {'x': '-2593/64', 'y': '-211/2', 'z': '-5969/96'}, openings P=(20, -37) Q=(20, -151/3) R=(20, -77) N1=(20, -153/4) N2=(5/2, -5977/100) N3=(20, -94) (unshifted, nook line x=0)



## 8. Guard number, canonical guards, correspondence

* `g(Φ) = n + m + A` (`m = 2·#inv + 3·#add`, `A = #add`).
* Regions (in this order): variables `0..n−1`, then for each slot `c` its inputs in template
  order, then its aux region (addition only).
* From a solution `v`: `γ_{σ_k} = (a_k, H + 2v_k − 1)`, `γ_{τ_j} = (b_j, 4v_{k(j)} − 2)` (the input
  copies the value of its variable exactly), `γ_{A_c} = g_c + I(v_x, v_y)` (§7.1).
* (c) direction: `v_k := (y(γ_{σ_k}) − H + 1)/2`.  Affine correspondence: the guard of variable `k`
  is at `(k·D_V, H − 1 + 2 v_k)`, i.e. the affine map `(x, y) ↦ ((y − H + 1)/2, x)` sends it to
  `(v_k, k·D_V)`.
* Copy types (monotonicity, [S §4.1]):

| constraint | x-input | y-input | z-input |
|---|---|---|---|
| `invGe x y`    | GE (`v_x ≥ w_x`) | GE | – |
| `invRevLe x y` | LE (`v_x ≤ w_x`) | GE | – |
| `addLe x y z`  | LE | LE | GE |
| `addGe x y z`  | GE | GE | LE |

## 9. Size

Number of vertices: `4 + 3n + 6|ones| + Σ_slots (template size) + 9m + 4m` (needles: 3 vertices
each, `W1, W3` on the ceiling and `W2` below for every segment, `+6` per `one`; copy nooks: 4
each; templates: 6, 8, 25, 25 vertices incl. needles).  Coordinates: numerators `O(H^4)`,
common denominator `Δ = lcm(2H−3, 2H−1, 2H−2) · Δ_T` with the template constant
`Δ_T = lcm(4, 48, 64, 32, 25, 16, 96, 100, 3, 8) = 9600`; `H = O(n·|Φ|)`.

## 10. Deviations from [S] (summary)

1. **Convex hall + glued features** instead of the free-form gallery of [S, Fig. 3]: all sight
   lines in the hall are free; every visibility upper bound is an *exit lemma* for one convex
   piece (proof plan L1.2) – no global "R1/R2" region arguments.
2. **Copy nooks on the ceiling without tubes**: by choosing input segments twice as long as
   variable segments (6 vs 3) and the ceiling at `2H`, both openings of every copy nook fall on
   the ceiling; the pocket is tiny (`ℓ = 6/(2H−3)`), so no corridors/tubes ([S, Lemmas
   4.4–4.6]) are needed.  The offset `e` (+12 / −16) is explicit.
3. **Inversion gadgets** designed by the perspectivity criterion with integer coordinates; the
   relation is an explicit Möbius identity.  `invRevLe` needs one opening on the floor and a
   pocket-hung needle.
4. **Addition gadgets**: the projective transformation of [S, Lemma 5.7] is replaced by the
   one-line identity `π_Q = μπ_P + (1−μ)π_R`; scales `k_x, k_y, k_z` replace the auxiliary points
   `K, J` of [S, Lemma 5.8]; `addGe` needs a recessed opening (bay).  The aux region is a single
   wedge cone intersected with the room.
5. **Guard regions** use thin "needle" wedges of height `H` (mouth `1/4`): all cones of a region
   stay in a slab of half-width 3, which makes the paper's "sufficiently narrow" (§5.3) explicit.
6. Floor at `y = −1` (forced by `invRevLe`), inputs `[0,6]`, variables `[H, H+3]`, ceiling `2H`.
