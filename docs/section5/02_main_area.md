# 02 — Base line, pockets, main hexagon

All coordinates exact rationals.

## Parameters

`N = max(4n+k, 2)`, `S = 200000·N²`, `ρ = 3/(2S)`, `δ = 9ρ`, `ε = ρ/12 = 1/(8S)`.
Slot `σ ∈ {0,…,4n−1}`: `a_σ = (27σ/2, 0)`, guard segment `s_σ = [a_σ, a_σ + (3/2,0)]`.
Shift of Theorem 54: `d_i = 27i/2 − 1/2` (`i < n`), so the guard `(x_i + d_i, 0)` lies on `s_i` and
specifies `x_i` (group 0 is right-oriented).

## The pocket of slot σ (vertices relative to `a_σ`, boundary order, polygon counter-clockwise)

```
m_L=(-6,1)  H'=(-1/2,0)  t0=(-3/2,0)  K'=(-1,-1/20)  C=(-1,-1)  D=(0,-1)
  [one-spike q1:  R0=(0,-2)  q1=(-1/2,-4)  Q'=(0,-21/5)]          (only if `one σ` ∈ Φ, σ<n)
u0=(0,-5)
  [one-spike q2:  q2=(1/2,-6)  (1/2,-5)]                            (only if `one σ` ∈ Φ, σ<n)
u1=(3/2,-5)  E=(3/2,-1)  G=(2,-1)  H=(2,0)  t1=(3,0)  K=(5/2,1/20)
```
followed by the next pocket's `m_L`, i.e. `m_R = (15/2, 1)` (mouths are contiguous: pitch 27/2).
Shape: a trapezoidal mouth part `T0` (between the slanted walls `m_L–H'` and `K–m_R`, above `y=0`),
a chamber `[-1,2]×[-1,0]`, a shaft `[0,3/2]×[-5,-1]`, a thin *roof spike* with tip `t0` and a thin
*floor spike* with tip `t1` (both of opening slope `1/10`).

Witness cones (interior wedge at the convex vertex, from `local_wedge`):

| witness | cone (relative coords) | consequence |
|---|---|---|
| `t0` | `{y ≤ 0, y ≥ -(x+3/2)/10}` | seen only inside the pocket room; seeing point has `y ≤ 0` |
| `t1` | `{y ≥ 0, y ≤ (3-x)/10}` | seen only inside the pocket room; `y ≥ 0`; cone meets `y=1` only at `x ≤ -7 < -6` |
| `u0` | directions between `(0,1)` and `(3/2,4)` | `x ≥ 0` along `y=0` (else crosses edge `C–D`) |
| `u1` | directions between `(-3/2,4)` and `(0,1)` | `x ≤ 3/2` along `y=0` (else crosses `E–G` or `G–H`) |
| `q1` | between `(1/2,-1/5)` and `(1/2,2)`; upper boundary line through `g=(1/2,0)` | `x ≥ 1/2` on `y=0` |
| `q2` | between `(0,1)` and `(-1/2,1)`; boundary `x = 1/2` | `x ≤ 1/2` on `y=0` |

* **Guard segment lemma** (Lemma 23 instance): a point of the polygon sees `t0,t1,u0,u1` iff it lies
  on `s_σ`.  Proof: cones of `t0,t1` give `y=0`, and both cones are disjoint from the *door* of the
  pocket room (`y = 1`, `x ∈ [-6, 15/2]`), so by the room lemma (03) the point is in the pocket room,
  hence `x ∈ [-3/2, 3]`; for `x ∈ [-3/2,0)` the segment to `u0` properly crosses the open edge
  `C–D` (crossing abscissa `4x/5 ∈ (-1,0)`); for `x ∈ (3/2, 11/4]` the segment to `u1` crosses
  `E–G`, for `x ∈ (11/4, 3]` it crosses `G–H`.
* With the `one` spikes, additionally `q1 ⇒ x ≥ 1/2`, `q2 ⇒ x ≤ 1/2`: the guard is at
  `g = a_σ + (1/2,0)`, value `1`.
* **Witness localisation.** `t0, t1` are seen only from the pocket room of σ (cones miss the door).
  `u0, u1, q1, q2` are seen from the pocket room and from a steep cone above it (slopes ≥ 3/2 in
  absolute value); these cones stay inside the main hexagon below its top edge `y = S+3N` and never
  reach `ℓ_r, ℓ_l` (at height `< S`, horizontal distance `≥ S − 54n`), hence avoid all unit doors.

## Main hexagon `H_M`

`w_l = (-6,1)` (= `m_L` of slot 0), `w_r = (54n-6, 1)` (= `m_R` of slot `4n−1`),
`v_r = (S, S)`, `t_r = (S, S+3N)`, `t_l = (X_L, S+3N)`, `v_l = (X_L, S)` with
`X_L = 54n − 12 − S`.  `H_M` = convex hull of these six points (the bottom side lies on `y = 1`
and consists of the pocket doors).  The polygon is

```
bottom wall (pockets of slots 0..4n-1, left to right), w_r, v_r,
  right units m = 0..R-1 (each: c0 … d0, see 04/06),  t_r, t_l,
  left units m = L-1..0 (mirror images, reversed),  v_l
```
(counter-clockwise; the edge `v_l → w_l` closes it).  The right units' doors `c0 d0` lie on
`x = S`, `y ∈ [S+1, S+3N-2]`; left ones mirrored.

## Main-area facts used later

* `H_M` is convex and contains every pocket door; the guard of slot σ (anywhere on `s_σ`) sees
  the closed pocket room of σ (union of the convex sets `T0 ∪ chamber`, shaft, spikes, each in a
  convex piece together with the guard) and every point of `H_M` with `x ∈ [a_σ.x−6, a_σ.x+15/2]`
  (the segment crosses `y = 1` inside the door, then stays in `H_M`).  The guards of slots `0`
  and `4n−1` see the two side triangles of `H_M` (crossing abscissa stays in the door because
  the side edges have slope `(S−1)/(S−54n+6) ≤ 6`).
* **Mirror symmetry.** `x ↦ 54n−12−x` maps the hexagon to itself and pocket σ (without spikes) to
  pocket `4n−1−σ`.
