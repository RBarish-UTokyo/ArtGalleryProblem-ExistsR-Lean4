# 06 — Assembly, guard count, canonical guards, denominators

## Boundary order (counter-clockwise)

```
V = [pocket chains of slots 0..4n-1, left to right]        (02)
    w_r = (54n-6, 1),  v_r = (S, S)
    for m = 0 .. R-1:   chain of right unit m              (c0, floor, c1, gadget, d1, Λ', d0)
    t_r = (S, S+3N),   t_l = (X_L, S+3N)
    for m = L-1 .. 0:   reverse(mirror(chain of left unit m, built in the right frame))
    v_l = (X_L, S)
```
`mirror(x,y) = (54n−12−x, y)`.  A left unit is built exactly like a right unit, in the *working
frame*, from the *working slots* `4n−1−σ` of its real slots σ (01 §units).

Unit `m` of a side: corridor (04) with `H = S+3m+1`; gadget template (05) placed at
`m_g = c1 + (1,−1)`, scale `1/S`.  The unit's vertical extent is `[H − 1.1, H + 1.4]`
(gadget at most `60/S` below `m_g`), so units are pairwise separated by a horizontal strip of
height `≥ 0.5`; this is the *box separation* used everywhere in the proofs.

| unit kind | template | slots (working frame, right) | guards in the unit |
|---|---|---|---|
| ≥-orientation (right), `g ∈ {0,1,2}` | `Add('orient')` | `(gn+i, 3n+i)` | 2 corridor SGs + 2 receivers + `r'_i` + 2 gadget SGs = **7** |
| ≤-orientation (left) | `Add('orient')`, mirrored | `(n−1−i, 4n−1−gn−i)` | **7** |
| ≥-add `x_a+x_b ≥ x_c` (right) | `Add('ge')` | `(a, n+b, 2n+c)` | 3 + 3 + 1 + 1 = **8** |
| ≤-add `x_a+x_b ≤ x_c` (left) | `Add('le')`, mirrored | real `(2n+b, n+a, c)`, working `(2n−1−b, 3n−1−a, 4n−1−c)` | **8** |
| inversion `x_a x_b = 1` (right) | `Inversion` | `(a, 3n+b)` | 2 + 2 + 0 + 1 = **5** |

**Guard count** `g = 4n + 42n + 16·k_add + 5·k_inv = 46n + 16 k_add + 5 k_inv`
(`one` constraints add no guards).  (The paper's count is `58n + 20k_1 + 5k_2`; ours differs
because our addition gadgets need one stationary guard instead of three and orientation gadgets
two.)

## Why the left ≤-gadgets are mirrors of right ≥-type templates

`mirror` maps slot σ to slot `4n−1−σ` and reverses orientation; a right-oriented guard of value
`x` becomes a guard whose *right-reading* `u = 1/2 + (offset from left endpoint)` equals `5/2 − x`.
Corridor copies preserve offsets from the left endpoint.  Therefore in the working frame:
* ≤-orientation `x(s_{gn+i}) ≤ x(s_{3n+i})` reads `u(s'_1) + u(s'_2) ≥ 5/2` — exactly the
  `orient` template;
* ≤-add `x_a + x_b ≤ x_c` reads `u_b + u_a ≥ u_c + 5/2` — the `le` template (the `ge` template
  with `r_l` moved right by `5/2`, `r_j` right by `5/2`, `r'_i` left by `5/2`, `r_i` up by `5/2`;
  this is the mirror image of the paper's ≤-gadget, §5.11).

## Canonical guards for an assignment `x` (Theorem 54, ⇐ direction)

* slot σ: `a_σ + (t_σ, 0)` with `t_σ = x_{σ mod n} − 1/2` (groups 0–2), `t_σ = 2 − x_{σ mod n}`
  (group 3);
* every receiver: `m_g + (T_τ + (t, 0))/S` with `t` the offset of its slot (`3/2 − t` for left
  units, in the working frame, then mirrored);
* `r'_i`: same offset as the `τ`-maximal receiver (exact weak copy);
* all corridor and gadget stationary guards (fixed points).
The guard `(x_i + d_i, 0)` with `d_i = 27i/2 − 1/2` is the slot-`i` guard.

## Denominators and sizes

* main area, corridor grid points: denominators dividing `1024·S`;
* template points: fixed rationals; `L_T` = lcm of all template denominators (118 bits; it could
  be made small by choosing slot corners on a grid — the slots are currently placed at exact line
  intersections, which is harmless since `L_T` is a constant);
* **axis vertices** (per copied pair: `p_k, z'_k` and the two slot corners on lines through `p_k`
  on the umbra axis; `n0, n1` on the nook axis): denominators `1024·S·L_T·G` where `G` is the
  denominator of the axis line (an integer of `O(log S)` bits, depending on the pair).
On small instances (`N ≤ 15`) the numerators have 95–110 bits; the lcm `D` of all denominators
grows linearly in the number of units, i.e. it has **polynomially many bits** but is not a
polynomially bounded integer.  For `agpInt_erComplete` multiply by `D` (binary arithmetic).
04 §Exactness explains why a common polynomially bounded denominator is impossible with shared
umbra shadow corners.

## n = 0

Then Φ is empty (all indices `< 0` impossible).  Use the triangle `(0,0),(1,0),(0,1)`, `g = 1`,
`d ≡ 0`: every guard set has ≥ 1 guard, and `{(0,0)}` is a guard set (convex).
