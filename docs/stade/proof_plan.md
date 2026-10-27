# Proof structure: Stade's construction (point-boundary and point-point AGP are ∃ℝ-hard)

Companion of `docs/stade/construction.md` (notation, all coordinates).  Every lemma below is stated so that its proof uses
only

* the visibility API `ArtGallery/Vis/API.lean`: **T1** `not_sees_of_proper_cross`, **T2**
  `closure_subset_filled_of_convex`, `filled_eq_of_frontier_subset`, `local_halfplane`,
  `local_wedge`, `interiorLeft_of_bottom_edge`, `sees_comm`;
* `Jordan.filled_subset_square` (the region is bounded) and elementary facts about segments;
* explicit (in)equalities between rationals / polynomial expressions in the parameters
  (`norm_num`, `linarith`, `nlinarith`, `positivity`, `field_simp`, `decide` on verified checkers).

The paper's "sufficiently narrow", "clearly", "straightforward" steps are replaced by the
explicit inequalities listed here.

---------------------------------------------------------------------------------------------------

## 0. Target theorems

```lean
namespace ArtGallery.Stade
/-- The polygon (rational vertices with common denominator) and the guard number. -/
def poly (n : ℕ) (Φ : List ETRINVREV.Constraint) : List (ℚ × ℚ)
def guards (n : ℕ) (Φ : List ETRINVREV.Constraint) : ℕ          -- = n + #inputs + #addition constraints
/-- abscissa and value map of variable `i`. -/
def varX (n Φ) (i : ℕ) : ℚ          -- = i * D_V
def varY0 (n Φ) : ℚ                 -- = H - 1    (guard of value v at (varX i, varY0 + 2 v))

theorem simple (hΦ : ∀ c ∈ Φ, c.VarsLt n) : (Polygon.mk ((poly n Φ).map ratPoint)).Simple
-- (a)
theorem card_le_of_boundaryGuard (hΦ) (G : Finset Point)
    (hG : (Polygon.mk ((poly n Φ).map ratPoint)).IsBoundaryGuardSet G) : guards n Φ ≤ G.card
-- (b)
theorem guardSet_of_sat (hΦ) {v : ℕ → ℝ} (hv : ∀ i, 1/2 ≤ v i ∧ v i ≤ 2) (hsol : ∀ c ∈ Φ, c.Holds v) :
    ∃ G : Finset Point, G.card = guards n Φ ∧ (Polygon.mk ((poly n Φ).map ratPoint)).IsGuardSet G ∧
      ∀ i < n, ((varX n Φ i : ℝ), (varY0 n Φ : ℝ) + 2 * v i) ∈ G
-- (c)
theorem sat_of_boundaryGuard (hΦ) (G : Finset Point)
    (hG : (Polygon.mk ((poly n Φ).map ratPoint)).IsBoundaryGuardSet G) (hcard : G.card = guards n Φ) :
    ∃ v : ℕ → ℝ, (∀ i < n, 1/2 ≤ v i ∧ v i ≤ 2) ∧ (∀ c ∈ Φ, c.Holds v) ∧
      ∀ i < n, ((varX n Φ i : ℝ), (varY0 n Φ : ℝ) + 2 * v i) ∈ G
```
Since `IsGuardSet → IsBoundaryGuardSet` (boundary ⊆ filled), (a)+(c) also hold for guard sets, so
the same polygon proves hardness of `AGP` (point-point) and `AGPPointBoundary`; with (b) one gets
`PolyRed ETRINVREV AGPPointBoundary` and `PolyRed ETRINVREV AGP` (and `AGPInt` after scaling by the
common denominator `Δ`, §11).  The affine correspondence is: the guard of variable `i` sits at
`(i·D_V, H − 1 + 2 v_i)`; the affine map `(x, y) ↦ ((y − H + 1)/2, x)` sends it to `(v_i, i·D_V)`
(form `(v_i + d_i, 0)` after swapping coordinates is not available because the segments are not
collinear; use the vertical form above, as allowed).

---------------------------------------------------------------------------------------------------

## 1. Generic tools (`Stade/Exit.lean`) 

### L1.1 Convex pieces
A *piece* is a convex polygon `K` given by its vertex list (counterclockwise) together with a
labelling of each side as **wall** or **opening**, such that every wall side is *exactly* one edge
of `P` traversed in the same direction (so `K` lies to the left of it).  (In the construction
every wall side is an edge; openings are mouths/windows/floor intervals between features.)
Additionally: at each vertex of `K` where two wall sides meet, these are consecutive edges of `P`
(a corner of `P`).

### L1.2 Exit lemma
`P` simple, `InteriorLeft`.  If `s ∈ K`, `P.Sees s p`, `p ∉ K`, then the segment `[s,p]` meets
some opening side of `K`.

*Proof.* Let `t* = sup {t ∈ [0,1] | s + t(p−s) ∈ K}` (K closed, convex ⇒ `{t | …}` is `[0,t*]`),
`e = s + t*(p−s) ∈ ∂K`, `t* < 1`.  Points `e_δ = s + (t*+δ)(p−s)` are in `filled` (segment) and
not in `K`.  Case analysis on the position of `e` on `∂K`:
(i) `e` in the relative interior of a wall side (= an open edge of `P`): by `local_halfplane`,
for small δ, `e_δ ∈ filled ↔ det(edge, e_δ) ≥ 0`; but `e_δ ∉ K` and all other side-constraints of
`K` are strict near `e`, so `det(edge, e_δ) < 0` – contradiction.
(ii) `e` a vertex of `K` joining two wall sides: by L1.1 it is a corner of `P` with exactly these
two edges; `local_wedge` says `filled` = the corner's closed wedge (convex corner, since `K` is
convex there) = `K` near `e` – contradiction.
(iii) otherwise `e` lies on a (closed) opening. ∎
Corollaries:

* **L1.3 (wedge cone)**: for a wedge (triangle `tip, m₁, m₂` with walls `tip m₁`, `tip m₂` and
  opening `m₁m₂`): `Sees p tip → p ∈ cone(tip; m₁, m₂) := {tip + λ(m₁−tip) + μ(m₂−tip) | λ, μ ≥ 0}`.
  (If `p` is in the triangle it is in the cone; otherwise `[tip,p]` crosses the mouth at
  `q = tip + λ(m₁−tip) + μ(m₂−tip)` with `λ+μ = 1`, so `p = tip + t(q − tip)`, `t ≥ 1`.)
* **L1.4 (nook PV)**: pocket = convex quadrilateral `lo, dn, up, hi` (walls `lo dn`, `up hi`, nook
  segment `hi lo`, opening `[dn, up]`).  If `s ∈ [lo, hi]` and `Sees p s` then
  `p ∈ pocket ∪ PV`, `PV := {beyond the mouth line} ∩ H(hi, dn ⊢ up) ∩ H(lo, up ⊢ dn)`
  (half-planes bounded by the two diagonals, containing the opposite mouth end).
  Proof: L1.2 gives `q ∈ [dn,up]` on `[s,p]`; write `p = s + t(q − s)`, `t ≥ 1`; then
  `det(hi, dn, p) = (1−t) det(hi,dn,s) + t det(hi,dn,q)` with both terms of the right sign (the
  computation in construction.md §5; `nlinarith`).
* **L1.5 (projection bound)**: same pocket, `p ∈ PV` beyond the mouth: every `s ∈ [lo,hi]` seen
  from `p` lies between the two *projections* of `p` through `dn` and `up` onto the nook line.
  (The line `p s` meets the mouth line inside `[dn, up]`; projection from `p` is monotone.)
  This is the only fact about "what a guard sees of a nook" used in (c).
* **L1.6 (chains)**: if `[s,p]` crosses an opening `ω` of `K` that is also an opening of the piece
  `K'` on the other side, then L1.2 applies again to `K'` from the crossing point.  Used only
  for the addition gadgets (room → pocket, room → bay → pocket).

### L1.7 Pieces in the region (T2)
For a piece `K`: if no edge of `P` meets `int K` and some point near a wall of `K` is an interior
point (from `InteriorLeft`), then `K ⊆ filled` (T2).  "No edge meets `int K`" is proved by
separation: every edge of `P` is either a wall of `K` (lies on `∂K`) or is separated from `int K`
by one of `K`'s side lines or by an axis-parallel line.  For the hall `𝓗` this is immediate
(every edge has `y ≤ −1` or `y ≥ 2H` or `x ∈ {x_L, x_R}`).

### L1.8 Visibility through a chain of pieces
If `[p,q] ⊆ K₁ ∪ … ∪ K_r` (pieces in `filled`) then `Sees p q`.  The decomposition of the segment
is by the crossing points with the openings (explicit parameters `t_i` computed by `field_simp`).

---------------------------------------------------------------------------------------------------

## 2. Polygon, simplicity, orientation, region

### L2.0 Definition (`Stade/Polygon.lean`) 
`poly n Φ` is the list of construction.md §3: left wall, `floor features`, right wall,
`ceiling features`.  Each feature is produced by a function `feature : FeatureSpec → List (ℚ×ℚ)`
of the data (abscissa, side, kind, template id, `H`).  Sorting is avoided: features are produced
**already in order** (variables by increasing `k`, slots by increasing `c`, inputs inside a slot
by template order; on the ceiling: inputs of slot `C−1` … `0`, then variables `n−1 … 0`, then copy
nooks – their order is by decreasing `x_N`, which is *not* monotone in `j`; produce them from the
list of inputs sorted by `x_N = 2a − b + e` using `List.mergeSort` on a computable key, **or**
avoid sorting entirely by placing copy nook `j` at `x_N − M·j`… — **decision**: keep the formula
`x_N = 2a − b + e` and sort (mergeSort is polytime and its permutation property is in Mathlib).

### L2.1 Orientation 
The left wall `(x_L, 2H) → (x_L, −1)` is an extreme edge (all vertices have `x ≥ x_L`): rotate
by `(x,y) ↦ (−y, x)` (an orientation-preserving isometry; transport of `Simple`, `filled`,
`boundary`, `InteriorLeft` via `ArtGallery/Invariance/Affine.lean`) and apply
`interiorLeft_of_bottom_edge`.  The transport of `InteriorLeft` along the rotation is
`ArtGallery/Stade/Generic/AffineOrient.lean`.

### L2.2 Simplicity (`Stade/Simple.lean`) 
Structure: the vertex list is `[corner] ++ F₁ ++ … ++ F_p ++ [corner, corner] ++ G₁ ++ … ++ G_q
++ [corner]`.  Generic lemma (**L2.2a**, reusable): *a closed polyline that is the
concatenation of chains `C_i`, each contained in a closed "box" `B_i`, is simple if (1) each
chain is simple (as an open polyline), (2) `B_i ∩ B_j = ∅` for non-adjacent `i, j`, (3) adjacent
chains share exactly their common endpoint and their boxes meet only there.*  Here:
* floor chains live in `x`-intervals `[x_start, x_end] × [−1−H−300, −1]`, ceiling chains in
  `[x_start, x_end] × [2H, 4H]`, the connecting floor/ceiling edges are the gaps;
* intervals are disjoint by the separation inequalities of §3 (`omega`/`linarith` on the formulas);
* each chain is simple: needles (3 vertices) trivially; copy pockets: convex quadrilateral (sign
  of four determinants – symbolic in `a, b, H`, `nlinarith`); gadget chains: **fixed** rational
  lists → `Irrational.Checker.simpleCheck` by `decide` on the template (translation invariance of
  simplicity) after replacing the `H`-dependent needle tips by a symbolic argument: needle tips
  `(s, β(s) − H)` are below everything else in the template, so a template chain with tips moved
  to depth `−H` is simple iff it is simple with depth `−H₀` for `H₀ = 1000` (monotonicity in the
  depth; prove: the two needle edges are vertical/near-vertical and only lengthen) .
* the polygon has ≥ 3 distinct vertices.

### L2.3 Region (`Stade/Region.lean`) 
`filled = 𝓗 ∪ ⋃ pieces` where the pieces are: wedge triangles, copy pockets, the `invGe` corridor
+ pocket, the `invRevLe` corridor + pocket (+ needle), each addition room + bay + three pockets +
needles.  Proof: `⊇` by L1.7 per piece; `⊆` by `filled_eq_of_frontier_subset` with
`U := 𝓗 ∪ ⋃ pieces`: `U` closed (finite union of closed convex polygons), `boundary ⊆ U` (each
edge is a wall of a piece), `frontier U ⊆ boundary` (a point of `U` off the boundary is interior
to `U`: either interior to a piece, or on an opening shared by two pieces, where the two half-discs
are in the two pieces), `U ⊆ filled` (⊇ part), `U \ boundary ≠ ∅`.
*Only (b) needs `⊆`; (a) and (c) use only L1.2–L1.5.*

---------------------------------------------------------------------------------------------------

## 3. Parameters and separation inequalities (`Stade/Params.lean`) 

With the definitions of construction.md §2 (`D_V = 600C + 50`, `H = max(1000, (n−1)D_V + 1200C)`,
`X_0 = H + (n−1)D_V`, `a_k = k D_V`, input abscissae `b = X_0 + c·1200 + δ` with template offsets
`δ ∈ [30, 600]`):

* **S1** `H ≤ b − a ≤ 2H` for every input `b` and variable `a`.
* **S2** distinct segment regions are `> 6` apart (= twice the slab half-width 3): variables
  `D_V ≥ 650`; inputs of one slot by the template table; inputs of different slots `≥ 1200 − 600`;
  inputs vs variables `≥ H`.
* **S3** copy pockets: `x_N(j) ∈ [−2H − 16, −1]` and `|x_N(j) − x_N(j')| ≥ 6` for `j ≠ j'`
  (cases same/different variable as in construction.md §5).
* **S4** all ceiling features lie in `x ∈ (x_L, x_R)` and `y ∈ [2H, 4H]`, all floor features in
  `y ∈ [−1 − H − 300, −1]`; template chains lie in their slot `[g_c, g_c + 1200)`.

---------------------------------------------------------------------------------------------------

## 4. Guard regions and the counting argument

### L4.1 Wedge cones 
For each wedge `w` of a segment region `r` at abscissa `s`: `cone(w) ∩ {y_min ≤ y ≤ y_max} ⊆
Slab_r := {|x − s| ≤ 3}` (explicit: the two rays from the tip; e.g. `W1`: tip `(s,3H)`, rays
`x = s` and `x = s + σ(3H − y)/(4H)`, and `(3H − y_min)/(4H) ≤ (4H+300)/(4H) < 3`).
For the aux wedge of an addition room: `cone(w) ∩ room ⊆ room` and `cone(w)` meets no opening of
the room except its own mouth (template inequalities, `decide`) ⇒ (L1.2 on the room) every viewer
of the aux tip lies in `room ∪ (aux wedge triangle)` (**L4.1'**).

### L4.2 Viewer sets of primaries are pairwise disjoint 
`Sees p tip(W1_r) → p ∈ filled ∩ cone ⊆ Slab_r` (L1.3, L4.1, `filled_subset_square` replaced by
the trivial bound `filled ⊆ {y_min ≤ y ≤ y_max}` – prove the latter like `filled_subset_square`
using vertical rays); aux: `⊆ room_c`.  Slabs are pairwise disjoint (S2) and every room is
disjoint from every slab (template + S2: the room of slot `c` meets only the slabs of its own
inputs, and `cone ∩ room` avoids them – template inequality).

### L4.3 Boundary pigeonhole (generic, file `Stade/Counting.lean`) 
Let `G` be a boundary guard set, `m_1, …, m_g` boundary points with pairwise disjoint viewer
sets `V_r ⊇ {p | Sees p m_r}`.  Then `g ≤ |G|`; if `|G| = g` there is a bijection `r ↦ γ_r ∈ G`
with `γ_r ∈ V_r` and `Sees γ_r m_r`; and for every boundary point `w` whose viewer set is
disjoint from all `V_{r'}`, `r' ≠ r`, the guard seeing `w` is `γ_r`.  (Finset cardinality; the
same argument as `Vis.guards_in_region` but for `IsBoundaryGuardSet`.)

**(a)** follows with `m_r = tip(W1_r)` / aux tips.

### L4.4 Guard positions when `|G| = g` 
For a segment region `r`: `γ_r` sees the tips of `W1, W2, W3` (and `W4, W5`), hence lies in the
intersection of their cones (L1.3), which is `{s} × [y_lo, y_hi]` (resp. the single point of value
1) – an explicit intersection of half-planes (`linarith`).  For an aux region: `γ ∈ cone ∩ (room ∪
aux triangle) =: A_c`.

---------------------------------------------------------------------------------------------------

## 5. Copy nooks (`Stade/Copy.lean`) 

Notation of construction.md §5; `Δ = b − a ∈ [H, 2H]`, `ℓ = 6/(2H−3)`.

* **L5.1 (homothety)** `P_σ` and `P_τ` are on the ceiling, `σ(u) := (a, H + 3u)`,
  `τ(u) := (b, 6u)` (`u ∈ [0,1]` relative position, `u = (2v−1)/3`): the line through `σ(u)` and
  `P_σ` meets `x = x_N` at height `N_top − ℓu`; same for `τ(u)` and `P_τ`. (`field_simp; ring`.)
* **L5.2 (pocket)** the quadrilateral `N_bot, L_m, R_m, N_top` is convex and counterclockwise
  (four determinant signs; uses `e ≠ 0`, `H ≥ 1000`, S1).
* **L5.3 (non-restriction)** GE: for `u ∈ [0,1]` the projection of `σ(u)` through `R_m = P_τ` is
  `≥ N_top` and the projection of `τ(u)` through `L_m = P_σ` is `≤ N_bot`.  Reduces to
  `e(H+3) ≥ Δ(5 + ℓ/2)` resp. `e(H+3) ≥ Δ(5 − ℓ/2)` … (construction.md §5).  LE symmetric.
* **L5.4 (coverage ⇒ inequality)** GE: if every point of `[N_bot, N_top]` is seen by `σ(u)` or
  `τ(w)` (and by no other guard, L5.5), then `u ≥ w`.  By L1.5 + L5.1 + L5.3: `σ(u)` sees only
  heights `≥ N_top − ℓu`, `τ(w)` only `≤ N_top − ℓw`; if `u < w` the point at height
  `N_top − ℓ(u+w)/2` is unseen.
* **L5.5 (exclusion)** the PV region of the copy nook of input `j` (variable `k`) contains no
  point of any other segment region and no point of any aux region.  Explicit: PV is bounded by
  the lines `ℓ_1 = N_top L_m` (through `σ_bot` for GE) and `ℓ_2 = N_bot R_m` (through `τ_top`);
  - at the variable band `y ∈ [H, H+3]`: `PV ⊆ {|x − a| ≤ 15}`, and other variables are `≥ 650`
    away;
  - at the input band `y ∈ [0,6]`: `PV ⊆ {|x − b| ≤ 27}`; other inputs are `≥ 60` away (template
    input gaps) or in other slots;
  - between the bands no guard region exists; below `y = −1` the PV region is to the right of
    `b − 13` and above the line through `τ` with slope `−1`, which avoids every aux region (rooms
    lie at least 40 left-below of their inputs' copy cones – template inequality T7);
  each item is a pair of linear inequalities in `(a, b, x_N, H)`, proved by `nlinarith` from S1.
  (the bounds 15 / 27 are loose: on test instances with `H ≤ 14500` the maxima are
  12.40 / 24.80.)
* **L5.6 (positive visibility, for (b))** `σ(u)` sees `{q ∈ pocket | q above the line σ(u)P_σ}`
  and `τ(w)` sees the part below `τ(w)P_τ`; for `u = w` the union is the whole pocket (the two
  chords `P_σ – π_σ(u)` and `P_τ – π_τ(u)` do not cross because their endpoints alternate on the
  pocket boundary).  Sight lines: hall (convex) + pocket (convex), L1.8.

---------------------------------------------------------------------------------------------------

## 6. Inversion gadgets (`Stade/Inversion.lean`) 

All coordinates are fixed rationals translated by `g_c` (construction.md §6).

### invGe (`v_x v_y ≥ 1`)
* **L6.1** projections (x-input at local `40`, y-input at `100`, nook `[J,I]` on `y = −78`):
  `π_P(v) = 40 + 3(v+19)/(v+1)`, `π_Q(v) = 40 + 3(1+19v)/(1+v)` (abscissae on the nook line);
  `π_P(2) = J`, `π_P(1/2) = I`, `π_Q(1/2) = J`, `π_Q(2) = I`.
* **L6.2** the x-guard sees only `[π_P(v_x), I]`, the y-guard only `[J, π_Q(v_y)]` (L1.5 with
  non-restriction: projections through `Q` of the x-input are `≥ I`, through `P` of the y-input
  `≤ J` – four rational inequalities).
* **L6.3** covered ⇒ `π_P(v_x) ≤ π_Q(v_y)` ⇒ `(v_x+19)(1+v_y) ≤ (1+19v_y)(v_x+1)` ⇒ `v_x v_y ≥ 1`.
* **L6.4 (exclusion)** PV = above `y = −6`, between the arms `y = −2(x−40)` (left, slope −2) and
  `y = 2(x−100)`; no other guard region meets it: variables are `≥ H` to the left at height `H`
  (`H > (H+3)/2`), other inputs are outside `[39, 101]` at heights `≤ 6`, aux regions are below
  the floor.  (The arms are steeper than every copy line – this replaces [S, Lemma 5.2] (R2).)
* **L6.5 (positive)** for `v_x v_y ≥ 1` the two guards see the whole pocket + corridor
  (corridor: the x-guard is in the V, which contains the corridor; chords argument).

### invRevLe (`v_x (5/2 − v_y) ≤ 1`)
* x-input at local `60`, y-input at `104`; `P = (59,−1)` (on the floor), `Q = (80,−8)`, nook
  `[J,I] = [(38,−22),(56,−22)]`, corridor triangle `P, Q, (101,−1)`.
  `π_P(v) = 60 − 4(5+v)/(4v−1)`, `π_Q(v) = 104 − 48(5+v)/(3+2v)`; covered ⟺
  `π_P(v_x) ≤ π_Q(v_y)` ⟺ `v_x(5/2 − v_y) ≤ 1` (polynomial identity after clearing the positive
  denominators `4v_x − 1`, `3 + 2v_y`).
* The x-input's `W2` hangs from the pocket wall `IQ` (`β(x) = −22 + 7(x−56)/12`); its cone passes
  through pocket, mouth and corridor (L1.8).
* PV = region above `y = −1`… bounded by the line `IP` (slope 7, through the top of the x-input)
  and the line `JQ` (slope 1/3, through the bottom of the y-input); it goes *up-right*, away from
  all variables; at the input band it lies in `[59, 122]` (local coordinates; exact: `[59.14, 122]`) (other inputs are `≥ 60` away in the
  slot layout).

---------------------------------------------------------------------------------------------------

## 7. Addition gadgets (`Stade/Addition.lean`) 

Template data: construction.md §7 (nook line `x = 30`, opening line `x = 50`, inputs at
`b_x, b_y, b_z`, shadows `s_i(v) = n_i + k_i(n_i − (4v − 2))`).

* **L7.1 (projection identity)** For a point `a = (a₁, a₂)` with `a₁ > 50` and an opening
  `O = (50, o)`, the projection of `a` through `O` onto `x = 30` is `π_O(a) = s·o − (s−1)a₂` with
  `s = (a₁ − 30)/(a₁ − 50)`.  Hence `π_Q = μ π_P + (1−μ) π_R` since `Q = μP + (1−μ)R` (`ring`).
  (This replaces the projective transformation of [S, Lemma 5.7].)
* **L7.2 (input shadows)** homothety through `N_i`: the x-input at value `v` projects to
  `s_x(v) = c_x − 4k_x v`, etc., with `μk_x = (1−μ)k_y = k_z` and `μc_x + (1−μ)c_y = c_z`
  (template identities, `norm_num`).
* **L7.3 (what each guard sees)** by L1.5: addLe: aux sees of nook x only heights `≥ π_P(a)`,
  of nook y only `≥ π_R(a)`, of nook z only `≤ π_Q(a)`; input x sees only `≤ s_x(v_x)`, etc.
  (non-restriction inequalities for inputs: rational; for the aux: they are *not needed* for (c);
  for (b) they are needed only at the canonical aux point.)
* **L7.4 (coverage ⇒ relation)** (addLe) margins: nook x extends `marg` above `s_x(1/2)`, nook
  y above `s_y(1/2)`, nook z `marg` below `s_z(2)`.  Covered ⇒ `π_P(a) ≤ s_x(v_x)`,
  `π_R(a) ≤ s_y(v_y)`, `π_Q(a) ≥ s_z(v_z)` (else an explicit unseen point – here the margins are
  used) ⇒ `s_z(v_z) ≤ μ s_x(v_x) + (1−μ) s_y(v_y)` ⇒ `v_x + v_y ≤ v_z`.  addGe: all inequalities
  reversed, margins on the other side.  Requires only `a₁ > 50` for the aux guard, true for every
  point of `A_c` (template).
* **L7.5 (canonical aux point, for (b))** `I(v_x, v_y)`: `s = (s_x − s_y)/(p − r)`,
  `a₁ = 50 + 20/(s−1)`, `a₂ = (s p − s_x)/(s − 1)`.  Must show for all `(v_x, v_y) ∈ [1/2,2]²`
  (addLe: with `v_x + v_y ≤ 2`): `s > 1`, `I ∈ A_c` (cone ∩ room), and the aux non-restriction
  inequalities.  These are rational-function inequalities in two variables on a box –
  : prove by clearing denominators and `nlinarith`/`polyrith`-style certificates; if a certificate is hard,
  split the box into 4–16 sub-boxes (`interval_cases`-free: monotonicity in each variable
  holds because `s_x, s_y` are affine and `I` is a Möbius function of `(s_x, s_y)`).
* **L7.6 (exclusion)** the PV of each of the three pockets contains, among all guard regions,
  only its own input and (part of) `A_c`.  Template inequalities (fixed rationals) + S2 for
  regions of other slots (they are farther than the template's PV band extent).  
  This is the binding design constraint: the distance from a pocket's PV
  band (`y ∈ [0,6]`) to the nearest foreign input segment is 14.16 / 17.02 / 52.83 (addLe, three
  pockets) resp. 8.54 / 9.05 / 62.47 (addGe); the needle slab (half-width 3) fits in each.
* **L7.7 (bay, addGe)** the z-input and every aux point see the z-nook through the bay
  `N1 N2 Q`: their sight lines through `N2` cross `x = 50` between `Q` and `N1` (template
  inequalities); the room boundary is non-convex at `N1` and `Q` only; pieces: room (convex),
  bay (triangle), pockets.
* **L7.8 (positive)** for a solution: aux at `I(v_x, v_y)`, every nook covered (chords argument),
  the room (convex) and the aux wedge seen by the aux guard, the bay seen by the z-input, the
  room-hung needles seen by their inputs through window + room.

---------------------------------------------------------------------------------------------------

## 8. Assembling (c) (`Stade/Lower.lean`) 

Given a boundary guard set `G` with `|G| = g`:
1. L4.3 + L4.2: guards `γ_r` bijectively assigned; L4.4: positions in the regions; define
   `v_k` from `γ_{σ_k}` (`v = (y − H + 1)/2 ∈ [1/2,2]`), input values `w_j` likewise, aux points.
2. `one x` ⇒ `v_x = 1` (L4.4 with `W4, W5`).
3. For each nook: its segment consists of boundary points; each is seen by some guard of `G`,
   which must lie in `pocket ∪ PV` (L1.4); no guard lies in a pocket (pockets are disjoint from
   all regions – S3/S4/template), so it lies in `PV`, hence is one of the designated guards
   (L5.5, L6.4, L7.6).  Apply L5.4 / L6.3 / L7.4.
4. Compose with the copy inequalities using monotonicity (construction.md table §8):
   `invGe`: `v_x ≥ w_x, v_y ≥ w_y, w_x w_y ≥ 1 ⇒ v_x v_y ≥ 1`; `invRevLe`: `v_x ≤ w_x`,
   `v_y ≥ w_y` ⇒ `v_x(5/2−v_y) ≤ w_x(5/2−w_y) ≤ 1`; `addLe`: `v_x ≤ w_x, v_y ≤ w_y, v_z ≥ w_z`;
   `addGe`: reversed.  (`nlinarith` with positivity of the factors.)

## 9. Assembling (b) (`Stade/Guarding.lean`) 

Guards: `γ_{σ_k} = (a_k, H + 2v_k − 1)`, `γ_{τ_j} = (b_j, 4v_{k(j)} − 2)`, `γ_{A_c} = I(v_x, v_y)`
(translated).  By L2.3, `filled = 𝓗 ∪ ⋃ pieces`; each piece is seen by a designated guard:
* `𝓗` by any guard in `𝓗` (convex, T2) – e.g. `γ_{σ_0}`;
* each wedge triangle by the guard of its region: the guard lies in the cone beyond the mouth,
  so for `z` in the triangle `[γ, z]` crosses the mouth (cone convexity) – L1.8 with pieces
  `𝓗`/room and the triangle;
* copy pockets L5.6, inversion pockets + corridors L6.5, addition rooms/bays/pockets/needles L7.8.
Distinctness of the `g` guards: they lie in pairwise disjoint regions.

## 10. Polynomial time (`Stade/PTime.lean`) 
`poly n Φ` uses only `List.range`, `map`, `flatMap`, `mergeSort` (copy nooks), arithmetic on
`ℚ` with numerators/denominators bounded by `O(H³)` (copy nooks: denominators `2H−3`, `2H−1`,
`2H−2`; wedges: `2H−3`, `2H−1`; templates: fixed).  Encoding into `FracPoint` and the bit-length
bound are as in the AAM reduction (`ArtGallery/Hardness/`).  For `AGPInt`: multiply by
`Δ = 4·(2H−3)(2H−1)(2H−2)·Δ_T` (`Δ_T` = lcm of template denominators, a constant).

## 11. Lean files

Stade's construction lives in `ArtGallery/Stade/` (54 files, 19,713 lines).

| file | lines | content |
|---|---:|---|
| `Stade/API.lean` | 54 | Stade's construction: the three correctness statements (interface) |
| `Stade/AdditionAlg.lean` | 601 | Stade construction, §7: algebra of the addition gadgets |
| `Stade/AdditionCover.lean` | 620 | Stade construction, §7: positive visibility in the addition gadgets (generic part, `addLe`) |
| `Stade/AdditionCoverGe.lean` | 485 | Stade construction, §7: positive visibility in the addition gadget `addGe` |
| `Stade/AdditionGeom.lean` | 927 | Stade construction, §7: geometry of the addition gadgets (generic part and `addLe`) |
| `Stade/AdditionGeomGe.lean` | 696 | Stade construction, §7: geometry of the addition gadget `addGe` |
| `Stade/Chains.lean` | 733 | Simplicity of polygons assembled from chains |
| `Stade/Copy.lean` | 456 | Stade construction, §5: the copy nooks (geometry) |
| `Stade/CopyAlg.lean` | 1008 | Stade construction, §5: algebra of the copy nooks |
| `Stade/Counting.lean` | 323 | Counting for boundary guard sets; global bounds of the region (proof plan L4.3, L2.1, L4.2) |
| `Stade/Exit.lean` | 549 | The exit lemma and its corollaries (proof plan L1.2–L1.8) |
| `Stade/Generic/AffineOrient.lean` | 135 | Orientation under affine maps (proof plan L2.1, §12 item 4) |
| `Stade/Generic/Fan.lean` | 309 | Rooms made of glued pieces (proof plan L1.6) |
| `Stade/Generic/Glue.lean` | 158 | Pieces glued along openings (proof plan L2.3, §12 item 5) |
| `Stade/Generic/Piece.lean` | 512 | Convex pieces (proof plan L1.1) |
| `Stade/GuardAdd.lean` | 304 | The canonical guards see the addition gadget `addLe` (proof plan L7.8) |
| `Stade/GuardAddGe.lean` | 259 | The canonical guards see the addition gadget `addGe` (proof plan L7.7, L7.8) |
| `Stade/GuardCanon.lean` | 188 | The canonical guards: membership and distinctness |
| `Stade/GuardCeil.lean` | 272 | The canonical guards see the ceiling features (proof plan §9) |
| `Stade/GuardCopy.lean` | 68 | The canonical guards see the copy pockets (proof plan L5.6) |
| `Stade/GuardDefs.lean` | 134 | The canonical guard set of a solution (construction.md §8, proof plan §9) |
| `Stade/GuardGadgetAPI.lean` | 49 | Interface for fact (b): the region decomposition (proof plan L2.3) |
| `Stade/GuardInv.lean` | 211 | The canonical guards see the inversion gadgets (proof plan L6.5) |
| `Stade/GuardRegion.lean` | 130 | The region of Stade's polygon as a union of convex pieces, and the canonical guards |
| `Stade/GuardSlots.lean` | 148 | The canonical guards see the gadget slots (proof plan §9) |
| `Stade/GuardTools.lean` | 254 | Generic visibility tools for the canonical guard set (proof plan §9) |
| `Stade/GuardWedges.lean` | 215 | The canonical guards see the wedges (proof plan §9) |
| `Stade/Guarding.lean` | 270 | Stade's construction, fact (b): a solution gives a guard set (proof plan §9) |
| `Stade/Inversion.lean` | 859 | Stade construction, §6: the inversion gadgets (geometry) |
| `Stade/InversionAlg.lean` | 438 | Stade construction, §6: algebra of the inversion gadgets |
| `Stade/Lower.lean` | 183 | Stade's construction: the correctness statements (a) and (c) (proof plan §8) |
| `Stade/LowerAssign.lean` | 216 | Stade's construction: the lower bound (a) and the guard assignment (proof plan §4, §8.1) |
| `Stade/LowerCopy.lean` | 320 | Stade's construction, (c): the copy nooks (proof plan §8.3, L5.4, L5.5) |
| `Stade/LowerGadgets.lean` | 484 | Stade's construction, (c): the constraint gadgets (proof plan §8.3, L6.3, L6.4, L7.4, L7.6) |
| `Stade/Main.lean` | 253 | ETR reduces in polynomial time to `AGPInt` and to `AGPPointBoundary` (Stade's construction) |
| `Stade/NookAlg.lean` | 327 | Stade construction: algebra of nooks (generic part) |
| `Stade/PTimePoly.lean` | 316 | Stade's construction is polynomial-time |
| `Stade/PTimeREV.lean` | 177 | The reduction ETR → ETR-INV-REV is polynomial-time |
| `Stade/PTimeRat.lean` | 288 | Polynomial-time arithmetic on integers and rationals (unary codes) |
| `Stade/PTimeScale.lean` | 485 | Stade's polygon with integer coordinates |
| `Stade/Params.lean` | 221 | Stade's construction: global parameters |
| `Stade/Polygon.lean` | 185 | Stade's construction: the polygon |
| `Stade/Region.lean` | 641 | The region of Stade's polygon as a union of convex pieces (proof plan L2.3) |
| `Stade/RegionGen.lean` | 378 | Generic tools for the region decomposition (proof plan L2.3) |
| `Stade/RegionSP.lean` | 602 | The region of Stade's polygon: the pieces lie in the region (proof plan L2.3, L1.7) |
| `Stade/RegionTmpl.lean` | 424 | The convex pieces of the gadget templates (proof plan L2.3) |
| `Stade/RobustCheck.lean` | 359 | Robust simplicity checks for chains depending linearly on a parameter |
| `Stade/Simple.lean` | 284 | Simplicity of Stade's polygon (proof plan L2.2) |
| `Stade/SimpleCeil.lean` | 320 | Simplicity of Stade's polygon: the ceiling |
| `Stade/SimpleFloor.lean` | 212 | Simplicity of Stade's polygon: inputs and floor |
| `Stade/SimpleOrient.lean` | 57 | Orientation of Stade's polygon (proof plan L2.1) |
| `Stade/SimpleTools.lean` | 228 | Tools for the simplicity proof: needles, quadrilateral nooks, separation |
| `Stade/Templates.lean` | 270 | Stade's construction: the gadget templates |
| `Stade/Wedges.lean` | 1118 | Stade's construction: wedge cones and guard regions (proof plan L4.1, L4.2, L4.4) |

## 12. Notes on the proof

1. **Addition gadgets.**  Their correctness rests on template inequalities with small margins
   (PV exclusion: ≥ 14.16 (addLe) resp. ≥ 8.54 (addGe) units at the input band; the bay of
   `addGe`) and on two-variable inequalities for the canonical aux point (L7.5).  Every L7.5
   condition is affine in the aux point, hence (after multiplying by a positive factor) affine
   in the values, so no subdivision of the value box is needed (`Stade/AdditionAlg.lean`).
2. **Simplicity with `H`-dependent needle tips inside template chains** (L2.2) uses a
   monotonicity argument (`Stade/Simple*.lean`).
3. **Sorting of copy nooks** (L2.0) and the generic chain-simplicity lemma
   (`Stade/Generic/Piece.lean`, `Stade/SimpleTools.lean`).
4. **Orientation** uses transport along the rotation (`Stade/Generic/AffineOrient.lean`).
5. The region description (L2.3) uses a generic lemma on convex pieces glued along openings
   (`Stade/Generic/Glue.lean`, `Stade/RegionGen.lean`).
6. The boundary version of the Lemma 22/23 counting (L4.3) is `Stade/Counting.lean`.
