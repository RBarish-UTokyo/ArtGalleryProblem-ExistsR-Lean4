# How many variables does an ETR encoding of the AGP need? (open problem of §7.2)

[AAM] encode an instance of the art gallery problem (a polygon with `n` corners, `k` guards) as
an existential formula with `(n + k)^6` variables, and ask (§7.2) whether `Ω(k)` variables are
necessary. Since `2k` variables are needed to write down `k` guards, the question is whether the
dependence on `n` can be removed. This note records what the formalization proves about it.

## Upper bound: `2k` variables (proved)

`agp_inER_guard_variables` (point guards, the whole polygon guarded),
`agpBoundaryPoint_inER_guard_variables` (guards on the boundary, the whole polygon guarded) and
`agpPointBoundary_inER_guard_variables` (point guards, only the boundary guarded) state
polynomial-time reductions to ETR whose output formula on an instance with `g` guards uses only the variables
`x₀, …, x_{2g−1}`, the coordinates of the guards (`φ.VarsLt (2 * g)`).

All auxiliary variables of the §3 encoding of [AAM] are *definitional*: arrangement vertices,
centroids of cells, the polygon coordinates, the crossing-parity bits of the point-in-polygon
test and the breakpoint parameters of the visibility test are rational functions of the guard
coordinates and the input constants. They are eliminated:

* rational expressions are substituted; each sign condition `sign(N/D) ⋈ 0` becomes
  `sign(N·D) ⋈ 0 ∧ D ≠ 0`, the denominators being explicit;
* the parity of the crossing bits is written as a Boolean XOR formula (balanced recursion, size
  `O(n²)`) instead of a product of auxiliary `±1` values;
* breakpoint parameters `t_j = N_j / D_j` become case splits on `D_j = 0`.

The result is a quantifier-free formula of polynomial size and bounded degree in the `2g` guard
coordinates. (Lean: `ArtGallery/FewVars/`.)

## Lower bound: `Ω(k / log k)` under ETH (informal, not formalized)

An existential formula with `N` variables and `s` atoms of degree at most `d` can be decided in
time `(s·d)^{O(N)}` (Renegar; Basu–Pollack–Roy). A polynomial-time reduction producing formulas
with `poly(n)` atoms of degree `poly(n)` and `N(k) = o(k / log k)` variables would therefore
decide point-guard AGP on simple polygons in time `n^{o(k / log k)}`, which contradicts
Bonnet–Miltzow (*Parameterized hardness of art gallery problems*, ESA 2016) unless the
Exponential Time Hypothesis fails. So, for reductions of this kind, `Θ̃(k)` variables are
necessary and sufficient, conditionally on ETH. This argument is not formalized (ETH is a
conjecture, and the decision procedures and the hardness result are not in Mathlib).

## Literature

As of 2026-10-27 we found no later paper that settles the question explicitly. Bonnet–Miltzow
(2016) is the relevant lower bound; the `n^{O(k)}` algorithms (Efrat–Har-Peled) match it up to
the logarithmic factor.

[AAM] M. Abrahamsen, A. Adamaszek, T. Miltzow, *The Art Gallery Problem is ∃ℝ-complete*, J. ACM
69(1), Article 4 (2021).
