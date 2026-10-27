# Section 5 construction — 01 Overview and design decisions

Target: `etrinv_guard_correspondence` (Theorem 54 of Abrahamsen–Adamaszek–Miltzow, J. ACM 2021),
see `Challenge.lean`.  This directory holds the explicit construction
(`02_*`–`07_*`), the structure of the formal proof (`08_proof_plan.md`) and the template
certificates (`10_template_certificates.md`).

Files:

| file | content |
|---|---|
| `01_overview.md` | this file: global layout, notation, deviations from the paper |
| `02_main_area.md` | base line, pockets, `one`-spikes, the main hexagon, shifts `d_i` |
| `03_witness_tools.md` | the uniform proof tools (cones, rooms, stationary guards) used everywhere |
| `04_corridor.md` | corridors (slab grid, upper wall, nooks, umbras, stationary guards) |
| `05_gadgets.md` | gadget templates: ≥-add, ≤-add (mirror), orientation, inversion |
| `06_assembly.md` | the full vertex list, guard count `g`, canonical guards, denominators |
| `08_proof_plan.md` | proof structure, Lean files, lemma list, dependency graph |
| `10_template_certificates.md` | the template facts proved by certified computation |

## Notation (fixed for the whole construction)

* Instance: `Φ = [c_0, …, c_{k-1}]`, variables `x_0 … x_{n-1}` (all indices `< n`).
* `N := max(4n + k, 2)`.  Scale `S := C·N²` with `C := 200000` (the paper's constant).
  `ρ := 3/(2S)`, `δ := 9ρ = 27/(2S)`, `ε := ρ/12 = 1/(8S)`.
* **Slots.** `4n` base guard segments `s_σ`, `σ = 0 … 4n-1` (0-based; the paper's `s_{σ+1}`).
  Slot `σ` represents variable `σ mod n`; group `⌊σ/n⌋ ∈ {0,1,2}` is right-oriented,
  group 3 left-oriented.  `a_σ := (27σ/2, 0)`, `s_σ := [a_σ, a_σ + (3/2, 0)]`.
* **Values.** A point `(a_σ.x + t, 0)` of `s_σ` (`t ∈ [0, 3/2]`) specifies `1/2 + t` if `s_σ`
  is right-oriented and `2 − t` if left-oriented.  Hence `d_i := a_i.x − 1/2 = 27i/2 − 1/2`
  for `i < n` (group 0), which is the shift of Theorem 54.
* **Units.** Every gadget together with its corridor is a *unit*.  Right units hang on the
  vertical line `x = S` (`ℓ_r`), left units on `x = X_L := 54n − 12 − S` (`ℓ_l`).  Unit `m`
  of a side has its corridor entrance `c0 = (x_side, S + 3m + 1)`.

## The list of units (deterministic order)

Right side (`ℓ_r`), in this order, unit indices `m = 0, 1, …`:
1. for `i = 0 … n-1`, `g = 0,1,2`: **orientation unit** on slots `(gn + i, 3n + i)`
   enforcing `x(s_{gn+i}) + x^r(s_{3n+i}) ≥ 5/2` (i.e. value(s_{gn+i}) ≥ value(s_{3n+i}));
2. for every constraint `add a b c` (in list order): **≥-add unit** on slots
   `(a, n+b, 2n+c)` enforcing `x_a + x_b ≥ x_c`;
3. for every constraint `inv a b`: **inversion unit** on slots `(a, 3n+b)` enforcing
   `x_a · x_b = 1`.

Left side (`ℓ_l`), same indexing scheme:
1. for `i`, `g` as above: orientation unit on slots `(gn + i, 3n + i)` enforcing
   value(s_{gn+i}) ≤ value(s_{3n+i});
2. for every `add a b c`: **≤-add unit** on slots `(c, n+a, 2n+b)` enforcing `x_a + x_b ≤ x_c`.

`one a` constraints add two spikes to the pocket of slot `a` (no unit).
So `R := 3n + k_add + k_inv ≤ N` right units and `L := 3n + k_add ≤ N` left units.
Repeated indices are harmless: the slots of a unit are always pairwise distinct and increasing
(`a < n+b < 2n+c`, `a < 3n+b`, `gn+i < 3n+i`); `n = 0` gives an empty base line (handled in
`02_main_area.md`, a degenerate polygon with `g = 1`).

## Main deviations from the paper (each justified in the relevant file)

1. **Mirror principle.** Every left unit is the mirror image (`x ↦ 54n − 12 − x`, which maps
   slot `σ` onto slot `4n−1−σ` and swaps orientation) of a *right-type* unit.  Under the mirror,
   value(·) ≤ value(·) for two slots becomes a ≥-orientation constraint, and `x_a + x_b ≤ x_c`
   becomes "right-readings `u_a + u_b ≥ u_c + 5/2`", realised by the paper's ≤-add template
   mirrored.  Hence the Lean development proves the corridor lemmas only for the right side and
   transports them by the reflection (an isometry; `Sees`, `filled`, `Simple` are invariant).
2. **Pockets** are redesigned (the paper's Fig. 11 is under-specified): explicit 15–19-vertex
   pockets whose witness corners have *thin cones* (see `02`, `03`), which makes all
   "seen only from region A" statements one-line cone/door computations.
3. **Uniform proof tools** (`03_witness_tools.md`): every invisibility claim is either a cone
   claim at a convex vertex (from `local_wedge`) plus a *room lemma* (a segment leaving a
   sub-polygon cut off by a chord crosses the chord), or a single proper edge crossing
   (`not_sees_of_proper_cross`).  Every visibility claim is a convex-piece claim
   (`closure_subset_filled_of_convex`) on an explicit convex decomposition.
4. **Stationary guards** are convex vertices `p` with two general-position witness slots whose
   thin cones cross exactly at `p` (paper Fig. 6 left); umbra stationary guards are the corner
   where a vertical edge from the valley (or `d1`) meets an edge on the exact umbra axis.
5. **Addition gadgets** (paper §5.10–5.12) are completed with a single gadget stationary guard
   (the paper uses three), and the *enclosed* receiver `r_j` gets far witnesses (05 §Topology —
   an obstruction the paper handles only in its figures, see `docs/paper_issues.md` A3).  The inversion gadget uses the paper's numbers
   (the `f2` denominator is `25835`, as printed in the JACM version).
6. **Theorem 54's formal statement is false as written** for `n ≥ 2`; see 08 §0 for the
   counterexample and the fix.
7. **Denominators** (06 §Denominators).  Grid points have denominators dividing `1024·S·L_T`
   (`L_T` a fixed constant from the templates), *except* the vertices that must lie exactly on a
   pair's umbra or nook axis (and the witness slots on integer-slope lines through the umbra
   stationary guard): about 12 per copied pair.  04 §Exactness explains why this is unavoidable
   with shared shadow corners `c0, c1`.  Their denominators come from a list of `O(N)` integers of
   `O(log S)` bits, so the lcm `D` has polynomially many bits; for the integer variant multiply
   by `D`.
