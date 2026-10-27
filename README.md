# The art gallery problem is ∃ℝ-complete, in Lean 4

A Lean 4 and Mathlib formalization of M. Abrahamsen, A. Adamaszek and T. Miltzow, *The Art
Gallery Problem is ∃ℝ-complete* (J. ACM 69(1), 2021), together with the point-boundary variant
of J. Stade, *The Point-Boundary Art Gallery Problem is ∃ℝ-hard* (SoCG 2025), for an explicit
Turing-machine model. It covers the three art gallery variants known to be `∃ℝ`-complete:
point-point, boundary-point and point-boundary.

* **What Lean proves.** Deciding whether a simple polygon with rational vertex coordinates can be
  guarded by `g` guards is `∃ℝ`-complete in each of three variants: guards anywhere, the whole
  polygon guarded (point-point, also for integer coordinates); guards on the boundary, the whole
  polygon guarded (boundary-point); guards anywhere, only the boundary guarded (point-boundary).
  Along the way: ETR-INV is `∃ℝ`-complete; the art gallery
  problem reduces to ETR by formulas whose only variables are the `2g` coordinates of the guards
  (the paper's formulas use `(n + g)^6`, `n` the number of corners); the guard sets of the
  paper's Section 5 polygon correspond exactly to the solutions of the ETR-INV instance
  (Theorem 54) and to the solutions of an ETR formula (Theorem 55); every algebraic number is
  the coordinate of a guard in every optimal guard set of some polygon (Theorem 2); and some
  polygon with integer corners needs irrational guards (Theorem 4).
* **Axioms.** The proof uses exactly Lean's three standard axioms (`propext`,
  `Classical.choice`, `Quot.sound`). There is no `sorry`, no other axiom and no `native_decide`;
  large finite computations are checked by the kernel (`decide +kernel`). No external result is
  assumed: the black-box bound of Schaefer and Štefankovič used by the paper (its Corollary 18)
  is replaced by a self-contained proof.
* **Checking.** The Lean kernel checks the proof; Comparator checks that the solution proves the
  challenge statement and replays it with the toolchain's independent kernels (see
  [Checking](#checking)). The recorded runs are local; official Palomar verification has not been
  performed.

Author and maintainer: Robert D. Barish (rbarish@ims.u-tokyo.ac.jp).

## Contributions

1. **Reusable Lean material on the existential theory of the reals.** Quantifier-free formulas
   over the reals and their codes (`ETR.Formula`, the language `ETR`), the class `∃ℝ` with
   hardness and completeness under polynomial-time many-one reductions (`InER`, `ERHard`,
   `ERComplete`), the problems ETR-INV (equations `x = 1`, `x + y = z`, `x · y = 1` with all
   variables in `[1/2, 2]`) and ETR-INV-REV (Stade's inequality version), and the reductions
   ETR → ETR-INV → ETR-INV-REV, proved polynomial-time on the same machine model as the author's
   earlier entries on NP-completeness. The chain includes an elementary proof that a solvable system of
   equations `x = 1`, `x + y = z`, `x · y = z` has a solution of doubly exponentially bounded
   size (`ArtGallery/ETR/Ball.lean`), replacing the cited result of real algebraic geometry. The library also
   contains a general toolkit for visibility in simple polygons (`ArtGallery/Vis/`) and the
   Jordan curve theorem for polygons.
2. **The open problem of §7.2 (number of variables), partially answered.** [AAM] ask whether
   `Ω(k)` variables are necessary for an existential formula encoding an instance with `k`
   guards. `agp_inER_guard_variables`, `agpBoundaryPoint_inER_guard_variables` and
   `agpPointBoundary_inER_guard_variables` show that `2k` variables suffice for all three
   variants: the reductions to ETR use only the guard coordinates, independently of the number
   of corners. A matching lower bound of `Ω(k / log k)` holds conditionally on the
   Exponential Time Hypothesis, by an informal argument combining the `n^{O(N)}` decision
   procedures for formulas with `N` variables with the parameterized hardness result of
   Bonnet and Miltzow (ESA 2016); this argument is not formalized
   ([`docs/research/variable_count.md`](docs/research/variable_count.md)).
3. **The `∃ℝ`-complete art gallery variants**, each with membership and hardness:
   * **point-point** (point guards, the whole polygon; [AAM] Theorem 1), also for polygons with
     integer vertex coordinates;
   * **boundary-point** (guards on the boundary, the whole polygon; [AAM] §7.2). [AAM] state this
     variant in a remark; the formalization needs a modified construction, because the paper's
     addition gadgets cannot be laid out with all guard segments on the boundary (see
     [Issues found in the papers](#issues-found-in-the-papers));
   * **point-boundary** (point guards, only the boundary; [S], which settles the corresponding
     question of §7.2 of [AAM]).

## The statement

The statement is [`Challenge.lean`](Challenge.lean): the definitions of
[`ArtGallery/Spec.lean`](ArtGallery/Spec.lean) and of the machine model, followed by the
theorems. It states thirteen theorems in namespace `ArtGallery`:

```lean
theorem etrinv_erComplete : ERComplete ETRINV                          -- Theorem 16
theorem agp_inER : InER AGP                                           -- Theorem 13
theorem agp_inER_guard_variables :                                    -- §7.2
    ∃ f : Word → Word, PolyTime f ∧ (∀ w, AGP w ↔ ETR (f w)) ∧
      ∀ (V : List FracPoint) (g : ℕ), ∃ φ : ETR.Formula,
        f (encodeAGP V g) = φ.encode ∧ φ.VarsLt (2 * g)
theorem agp_erComplete : ERComplete AGP                               -- Theorem 1
theorem agpInt_erComplete : ERComplete AGPInt                         -- Theorem 1, integer corners
theorem agpBoundaryPoint_erComplete : ERComplete AGPBoundaryPoint     -- boundary-point
theorem agpBoundaryPoint_inER_guard_variables : …                     -- §7.2, boundary-point
theorem agpPointBoundary_erComplete : ERComplete AGPPointBoundary     -- point-boundary (Stade)
theorem agpPointBoundary_inER_guard_variables : …                     -- §7.2, point-boundary
theorem etrinv_guard_correspondence (Φ : List ETRINV.Constraint) (n : ℕ)
    (hΦ : ∀ c ∈ Φ, c.VarsLt n) : …                                     -- Theorem 54
theorem etr_guard_correspondence (φ : ETR.Formula) (n : ℕ)
    (hφ : φ.VarsLt n) : …                                              -- Theorem 55
theorem algebraic_guard_coordinate (α : ℝ) (hα : IsAlgebraic ℚ α) :
    ∃ V : List (ℚ × ℚ), (Polygon.mk (V.map ratPoint)).Simple ∧
      (∃ G, (Polygon.mk (V.map ratPoint)).IsOptimalGuardSet G) ∧
      ∀ G, (Polygon.mk (V.map ratPoint)).IsOptimalGuardSet G → ∃ p ∈ G, p.1 = α  -- Theorem 2
theorem irrational_guards_needed : …                                  -- Theorem 4
```

In words, beyond the completeness results:

* **Theorem 54.** For every ETR-INV instance `Φ` on the variables `x₀, …, x_{n−1}` there are a
  simple polygon with rational corners, a number `g` and rational shifts `d_i` such that every
  guard set has at least `g` guards, every guard set with exactly `g` guards contains the points
  `(x_i + d_i, 0)` for some solution `x`, and, for `x ∈ [1/2, 2]ⁿ`, `x` is a solution iff some
  guard set with `g` guards contains the points `(x_i + d_i, 0)`.
* **Theorem 55.** The same for an arbitrary ETR formula, with guards at `(c_i x_i + d_i, 0)`,
  `c_i ≠ 0` rational: the polygon has a guard set of size `g` if the formula is satisfiable,
  and every guard set of size `g` encodes a solution.
* **Theorem 4.** There is a simple x-monotone polygon with integer corners that can be guarded by
  three guards, while every guard set consisting of rational points has at least four guards
  (and one with four exists).

### Definitions

All definitions are in `Challenge.lean` with docstrings.

* **Machines and complexity.** Deterministic single-tape Turing machines over
  {blank, 0, 1, separator}, time = number of steps, polynomial bounds `c * (n + 1)^k`,
  `PolyTime f`, `PolyRed A B` (polynomial-time many-one reductions). These are reused verbatim
  from the author's Palomar entry [NPC].
* **ETR.** Terms with constants `0, 1` and `+, −, ·`; quantifier-free formulas with `=, <, ≤`,
  `¬, ∧, ∨` over the variables `x₀, x₁, …`; `ETR` is the set of codes of satisfiable formulas.
  `InER L` means `L` reduces to `ETR`; `ERHard` and `ERComplete` as usual.
* **ETR-INV.** Lists of constraints `x = 1`, `x + y = z`, `x · y = 1`; an instance is solvable if
  it has a solution with every variable in `[1/2, 2]`.
* **Codes.** Variable indices are written in unary; the numbers of an art gallery instance
  (numerators, denominators, integer coordinates, `g`) are written in binary.
* **Polygons and guarding.** A polygon is its list of corners in boundary order; it is simple if
  it has at least three distinct corners and any two distinct edges meet exactly in their common
  endpoints (collinear consecutive corners are allowed). Its region `filled` is the boundary
  together with the points whose component in the complement of the boundary is bounded. Two
  points see each other if the closed segment between them lies in the region. A guard set is a
  set of points of the region seeing every point of the region; a guard set on the boundary
  consists of boundary points and sees every point of the region; a boundary guard set consists
  of points of the region and sees every boundary point. These definitions are those of the
  author's Palomar entry [CHZ] on Chazelle's triangulation algorithm.
* **Problems.** `AGP`: codes of a list of rational corners (numerator/denominator pairs) and a
  number `g` such that the polygon is simple and has a guard set with exactly `g` points
  (equivalently at most `g`, since guards can be added). `AGPInt`: the same with integer corners.
  `AGPBoundaryPoint`: the same with guard sets on the boundary. `AGPPointBoundary`: the same
  with boundary guard sets.

## Relation to the papers

The proof follows [AAM] and [S]; the design notes in `docs/` describe every construction with
exact coordinates. The main points:

* **ETR-INV is `∃ℝ`-complete (§4 of [AAM]).** ETR → arithmetic circuits → the ETR-INV chain with
  the affine correspondence `y = εx + 7/8`. The scaling exponent comes from a self-contained ball
  theorem (`ArtGallery/ETR/Ball*`), proved by a perturbation and limit argument, instead of the
  cited Corollary 18.
* **Membership (§3 of [AAM]).** The witness lemma (arrangement cells and their centroids) and the
  formulas INSIDE and SEES are formalized; the `2g`-variable version eliminates every auxiliary
  variable (`ArtGallery/FewVars/`).
* **Hardness.** Theorem 1, its integer-coordinate version and the point-boundary result are
  proved through Stade's construction (`ArtGallery/Stade/`): ETR → ETR-INV-REV → one polygon that
  works for both the point-point and the point-boundary problem and has a common denominator of
  polynomial bit length, so that it can be scaled to integer coordinates. Theorem 2 is also
  derived from it (after a rotation). The paper's own Section 5 construction is formalized for
  Theorems 54 and 55 (`ArtGallery/Hardness/Sec5/`), with explicit pockets, corridors and gadget
  templates whose visibility facts are kernel-checked certificates. The boundary-point result is
  proved through a modification of the Section 5 construction (`ArtGallery/Hardness/BP/`): every
  guard segment is moved onto the floor of a shallow bay in the boundary whose side walls carry
  pinning spikes, the addition gadgets are re-laid out (their receivers exchange roles; the
  mechanism of [AAM] Lemma 41 is unchanged), and the construction is shown to be polynomial-time.
  The design and the reasons why Stade's construction and [AAM]'s layout do not work for
  boundary guards are in `docs/boundary_point/design.md`.
* **Theorem 4 (§2 of [AAM]).** The paper's polygon, scaled to integer coordinates
  (`ArtGallery/Irrational/`).
* **Not formalized.** The Picasso theorem (Theorem 3) and Theorem 56 on compact semi-algebraic
  sets: their published proof depends on a gap (see below), and they are universality statements
  that the complexity results do not need; their coordinate form is formalized as Theorems 54
  and 55. Also not formalized: the general-position modification of §7.1.

### Issues found in the papers

[`docs/paper_issues.md`](docs/paper_issues.md) lists the errors, gaps and imprecisions found in
the published arguments, with counterexamples or explanations. None of them affects the
formalized results. In short:

* [AAM] Lemma 21, used for Theorem 56 and the Picasso theorem, is not proved by the given
  argument: auxiliary variables encoding strict inequalities can be unbounded on a compact set,
  so the rescaling loses points (counterexample given). The statements remain true by the
  finiteness theorem for closed semi-algebraic sets.
* [AAM] Theorem 54, read literally, is false for `n ≥ 2` (two variables can share one guard); the
  formal statement quantifies over `[1/2, 2]ⁿ` on both sides.
* [AAM] §7.2 states the boundary-point variant as an easy adjustment of the construction; for
  the addition gadgets as laid out this is not possible (a receiver is enclosed by mandatory
  sight lines and cannot lie on the boundary), so the gadgets have to be re-laid out.
* [AAM] exposition gaps: the pockets of §5.8 are under-specified; the middle receiver of the
  addition gadgets is pinned by features that appear only in the figures; several sufficiency
  arguments stop at the critical segments.
* [S] Theorem 2.4: a constant `5/2` outside the allowed range (unused), and an interval property
  of [AAM]'s reduction that is read off from its proof rather than proved (proved here).

## Checking

The project pins Lean `leanprover/lean4:v4.35.0-rc2` and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```sh
lake exe cache get
lake build
./scripts/verify-comparator.sh                 # lake comparator with NanoDa and con-ron
```

The committed Lean files, including the generated certificate and data files, are the only inputs;
no source-generation step is needed. `scripts/verify-comparator.sh` runs Comparator as Palomar
does, with the toolchain's NanoDa and con-ron kernels; it needs `bwrap`. The record of the local run is in
[`docs/VERIFICATION.md`](docs/VERIFICATION.md).

## Layout

* `Challenge.lean`, `Solution.lean`, `comparator.json`: the Palomar statement, proof and
  Comparator configuration.
* `ArtGallery/Spec.lean`: every definition the statement uses.
* `Complexity/`, `PT/`: the machine model, P/NP-style classes, a register language and a
  framework for proving polynomial time (reused from earlier entries).
* `ArtGallery/ETR/`: circuits, the ball theorem, the ETR-INV chain and ETR-INV-REV.
* `ArtGallery/PTime/`: codes and polynomial-time proofs of the reductions.
* `ArtGallery/Membership/`, `ArtGallery/FewVars/`: membership in `∃ℝ`, and the `2g`-variable
  reductions.
* `ArtGallery/Stade/`: Stade's construction, its correctness and polynomial time.
* `ArtGallery/Hardness/Sec5/`: the Section 5 construction and Theorem 54.
* `ArtGallery/Hardness/BP/`: the boundary-point construction (bays, re-laid-out templates), its
  correctness and polynomial time.
* `ArtGallery/Irrational/`, `ArtGallery/Corollaries/`: Theorems 4, 2 and 55.
* `ArtGallery/Vis/`: visibility in polygons (blocking, cones, rooms, pinning, stationary guards,
  certificate checkers); `ArtGallery/{Geometry, Jordan, Existence, Invariance}/`: planar
  geometry, the Jordan curve theorem for polygons, triangulations and affine invariance.
* `scripts/verify-comparator.sh`: the local Comparator check.
* `docs/`: design notes for the three constructions (`docs/stade/`, `docs/section5/`,
  `docs/boundary_point/`), the issues
  found in the papers, the note on the number of variables, provenance and verification.

## Provenance

See [`docs/PROVENANCE.md`](docs/PROVENANCE.md) for the origin of every Lean file. The machine
model, the polynomial-time framework and part of the complexity library are reused verbatim from
the author's Palomar entries [NPC] and [MAX]; the polygon definitions and the planar-geometry and
Jordan-curve library are adapted from the author's entry [CHZ].

AI assistance is acknowledged. Claude Opus 5.5 (Anthropic) was used both for the Lean formalization and
to assist with the documentation, including this README, `formalization.yaml`, the
`Challenge.lean` header, the verification record and `scripts/verify-comparator.sh`. The generated
Lean files (certificates and construction data) were produced by Python programs with exact
rational arithmetic, written with the same assistance; these programs are not part of this
repository, and the files they produced are checked by the Lean kernel like all other files. See
`formalization.yaml` for the automation and review metadata.

Development date: 2026-10-27.

## References

* [AAM] M. Abrahamsen, A. Adamaszek, T. Miltzow. The art gallery problem is ∃ℝ-complete.
  Journal of the ACM 69(1), Article 4 (2021). Preliminary version STOC 2018.
* [S] J. Stade. The point-boundary art gallery problem is ∃ℝ-hard. SoCG 2025, LIPIcs 332,
  Paper 74. Full version arXiv:2210.12817.
* É. Bonnet, T. Miltzow. Parameterized hardness of art gallery problems. ESA 2016;
  arXiv:1603.08116.
* M. Schaefer, D. Štefankovič. Fixed points, Nash equilibria, and the existential theory of the
  reals. Theory of Computing Systems 60 (2017).
* [NPC] R. D. Barish. NP-completeness of SAT, 3-SAT and their variants (the Cook–Levin theorem)
  in Lean 4. Palomar, PALOMAR-2026-10-02-000013 v1 (2026).
  <https://palomar-registry.org/entry?id=PALOMAR-2026-10-02-000013&version=1>
* [MAX] R. D. Barish. MaxSNP-completeness and APX-completeness of MAX-3-SAT and 3-OCCURRENCE
  MAX-3-SAT (the PCP theorem and hardness of approximation) in Lean 4. Palomar,
  PALOMAR-2026-10-09-000010 v1 (2026).
  <https://palomar-registry.org/entry?id=PALOMAR-2026-10-09-000010&version=1>
* [CHZ] R. D. Barish. Linear-Time Triangulation of Simple Polygons (Chazelle's Algorithm) in
  Lean 4. Palomar, PALOMAR-2026-10-05-000003 v2 (2026).
  <https://palomar-registry.org/entry?id=PALOMAR-2026-10-05-000003&version=2>

## License

Apache License 2.0 ([`LICENSE`](LICENSE)). Mathlib and its dependencies retain their own
licenses.
