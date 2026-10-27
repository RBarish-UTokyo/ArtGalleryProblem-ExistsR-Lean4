# 04 — Corridors

Right side; left corridors
are mirror images (01, mirror principle).

## Data of one corridor

Input: the unit height `H = S + 3m + 1`, the copied slots `σ_1 < … < σ_p` (`p ∈ {2,3}`), and the
template left endpoints `T_τ` of the gadget's *receiver segments* `r_τ` (`τ = 0 … p−1`;
`τ(σ_k) = p − k`, i.e. the largest slot gets `τ = 0`).  Receiver segment
`r_τ = [m + T_τ/S, m + T_τ/S + (3/(2S), 0)]` with `m = c1 + (1,−1)`.

Corners: `c0 = (S, H)`, `c1 = c0 + (2,0)`, `d0 = c0 + (0, 2ρ)`, `d1 = c1 + (0, ρ)`;
local origin `O_c = c0 + (1,1)`; for a point with local coordinates `(X,Y)`:
`ζ = Y − X`, `ξ = Y + X`.

Slab centres (vertical offsets on the line `X = 0`):
* L-slabs: `Z(σ,γ) = ζ_o + σδ + γρ`, `ζ_o = (H − S)/S` (exact ζ of `o = ray(a_0,c0) ∩ {X=0}`),
* R-slabs: `Ξ(τ,γ) = ξ_ref + τδ + γρ`, `ξ_ref = −(T_0.x + 3/2 + T_0.y)/S`.

Requirement on the receivers (generalised Lemma 39): `T_τ.x + T_τ.y = T_0.x + T_0.y − 27τ/2`
(sums spaced by `27/2`), all `T_τ` in `[-50,50]²`.

## Upper wall Λ' (westward from `d1` to `d0`)

For the pairs in the order `k = 1 … p` (slot increasing = right to left), with
`Lw = Z(σ_k,2) − 2ε`, `Rw = Ξ(τ_k,2) − 2ε`, apex `u = (ζ,ξ) = (Lw, Rw)`:

1. `base_k` = `d1` for `k = 1`, else the **valley** `v_k = (ζ,ξ) = (Lw_{k−1}, Rw_k + ε/2)`
   (on the left wall of pair `k−1`, `ε/2` beyond the line `ξ = Rw_k`; see §Receiver conditions);
2. **umbra axis** `A_k` = line through `f0 = (b_σ c0) ∩ (b'_τ c1)`, `f1 = (a_σ c0) ∩ (a'_τ c1)`
   (`a,b` / `a',b'` left/right endpoints of `s_σ` / `r_τ`);
3. **stationary guard** `p_k = (base_k.x, A_k(base_k.x))` (convex vertex; edges `base_k → p_k`
   vertical, `p_k → z'_k` along `A_k`);
4. `z'_k = (x, A_k(x))`, `x = O_c.x + (ε/8)(⌈X*/(ε/8)⌉ + 1)` with `X* = Rw − Y_a`
   (`Y_a` = local height of `A_k` at the apex abscissa; `X*` is the abscissa of
   `A_k ∩ {ξ = Rw}` up to `< 10⁻³ε`): the grid abscissa rounded **up** plus one grid unit, so
   `z'_k` lies strictly east of `ξ = Rw`, at `ξ ∈ [Rw + ε/16, Rw + 5ε/16]` (Lean: `Good.xi_zp`);
5. **nook** at the apex: mouth `z1 = (ζ,ξ)=(Rw − y_N … )`, i.e. `z1` on `ξ = Rw`, `z0` on
   `ζ = Lw`, both at height `y_N = Y(u) − 3ε`; nook axis `A'_k` through
   `F0 = (b_σ z0) ∩ (b'_τ z1)`, `F1 = (a_σ z0) ∩ (a'_τ z1)`; top edge
   `n1 = (z1.x, A'_k(z1.x))`, `n0 = (z0.x, A'_k(z0.x))`; vertices `z1, n1, n0, z0`;
6. continue along `ζ = Lw` to the next valley (or to `d0` after the last pair).

So Λ' = `d1, [p_1, z'_1, z1, n1, n0, z0]_1, v_2, [p_2, …]_2, …, d0`.

Floor (eastward `c0 → c1`): for every pair `k` two **witness slots** on the lines through `p_k`
with slopes `2` and `4` (directions strictly inside the wedge of `p_k`):
`k_s = (p_k.x − (p_k.y − H)/s, H)`, tip `q = k_s + (−1/16, −s/16)`, third vertex
`k_s ∓ (ε/8, 0)` (west side for `s = 2`, east side for `s = 4`); slots sorted by abscissa.
Then `c1`, then the gadget chain.

All vertices are on the grid `(ε/8)ℤ²` shifted by `O_c` **except** `p_k, z'_k` (on `A_k`), the
slot vertices (on lines of slope 2, 4 through `p_k`) and `n0, n1` (on `A'_k`): their abscissae
are grid points or obtained from `p_k` by integer slopes, their ordinates are values of the exact
axis lines (structured denominators, see 06 §Denominators).

## Receiver conditions

The receiver `q = q_τ(t) = a'_τ + (t/S, 0)`, `t ∈ [0, 3/2]`, sits at local `(X, Y) ≈ (2, −2)`
(units), so its lines into the corridor have slope `≈ −1`: along them `ξ` drifts only by
`(ξ_b − ξ_q)/(ζ_b − ζ_q) ≈ 1600ε/(32S·ε)` per unit of `ζ`.  It sees the umbra region `U_k` next
to the edge `z'_k z1` and the nook only along lines passing **west of the reflex corner `z'_k`**
and **below the valley `v_k`** (`k ≥ 2`).  Necessary conditions (all three are affine in `t`):

* (Z) `det(q, z'_k, z1) ≥ 0`;  (V) `det(q, v_k, z1) ≥ 0`;  (W) `det(q, v_k, z'_k) ≥ 0`.

With `z1` on `ξ = Rw`, `z'_k` at `ξ ≥ Rw + ε/16` and `v_k` at `ξ = Rw + ε/2` they hold with margins
`≥ ε/8 − 0.01ε` (Z), `≥ ε/2 − 0.03ε` (V), `≥ 3ε/16` (W) (Lean: `Corridor/Receiver.lean`,
`Good.recv_zp`, `Good.recv_valley_z1`, `Good.recv_valley_zp`).  With `v_k` and
`z'_k` on (resp. within `±ε/16` of) `ξ = Rw`, (Z)/(V) would fail in most configurations (e.g. in
some inversion units), leaving points of the nook top edge and of `U_k` unseen.  The shifts cost at most `ε/4` in the margins of
the stationary-guard configuration (`p_k.x − z'_k.x ≥ 37.8ε`, `p_k.y − v_k.y ≥ 37.6ε`) and
leave the receiver's `d1`-lines (`ξ ≥ Ξ(τ,2) − ε = Rw + ε`) above `v_k`.

## Why exactness forces axis vertices (and why the copy is exact)

For a copy pair with shadow corners `k0,k1` at equal height the composite projection
`s_σ → A → r_τ` maps `a_σ ↦ a'_τ`, `b_σ ↦ b'_τ` and is affine iff `A` is the line `f0 f1`
(Steiner/Desargues: the pencils at `k0`, `k1` correspond projectively with the common line `k0k1`
self-corresponding, so the locus of intersections is a line).  Coverage of the open region just
above `A` (umbra) or of the top edge on `A'` (nook) by the two guards is equivalent to
"the crossing point of `p k0` and `q k1` lies on/below `A`" resp. "the two projections are
ordered", i.e. to `value(q) ≥ value(p)` (umbra) and `value(q) ≤ value(p)` (nook).  Since the stationary guard must see exactly the closed
half-plane below `A`, `A` must carry vertices; the height of `A_k` over `c0c1` is
`2H·(…)/G` with `G = S(Q−w) + Δ_σ` depending affinely on the slot, hence no fixed polynomial grid
contains all axes.

## Stationary guards of the corridor

`p_k` is a convex vertex with interior wedge "west along `A_k`" to "south" (exactly
`[180°, 270°]` since `base_k → p_k` is vertical).  Witnesses: the two floor slots `q_a` (slope 2,
cone on the west side of its line) and `q_b` (slope 4, cone on the east side).  Near `p_k` the
cone of `q_a` lies in the half-plane `H_a` containing the directions `[63.4°, 243.4°]`, that of
`q_b` in `H_b ⊇ [256°, 76°]`; `H_a ∩ H_b ∩ (p_k + wedge) = {p_k}`, hence
`V(q_a) ∩ V(q_b) = {p_k}` (SG lemma, 03).  Both slots lie at directions strictly inside the wedge,
so `p_k` sees the whole slots (their interiors must be seen by someone — a witness on a *boundary*
ray of the wedge would have an interior that no guard sees; this is why a
needle on the axis cannot be used).
`p_k` sees: everything of the corridor left of `x = p_k.x` and below `A_k` (in its wedge); nothing
above `A_k`; nothing right of `x = p_k.x` (in particular nothing beyond the window `c1d1` for
`k = 1`, which it sees only along the line `x = c1.x`).  The slope-4 slots of different pairs lie
on parallel lines (disjoint `m`-witness cones); the slope-2 lines may cross other pairs' slope-4
cones, which is why pinning is done left to right (08 §5).

## Bands (the slab lemma, cf. paper Lemmas 32/33/39)

For `p ∈ s_σ`: inside `V = O_c + [−38Nρ, 38Nρ]²` the lines `p c0` and `p d0` are within vertical
distance `ε` of the L-slab centres `Z(σ,γ)` with `γ ∈ [0,1]` resp. `[2,3]` (monotone in the
position of `p`).  For `q ∈ r_τ` the lines `q c1`, `q d1` are within `ε` of `Ξ(τ,γ)`,
`γ ∈ [0,1]` resp. `[2,3]`.  Consequently the corridor part seen by `s_σ` lies in the band
`ζ ∈ [Z(σ,0)−ε, Z(σ,3)+ε]` and these bands are pairwise disjoint (gap `6ρ − 2ε`); likewise for
receivers.  Explicit inequalities: 08 §Corridor inequalities.

