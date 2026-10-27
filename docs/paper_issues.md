# Issues found in the source papers

Errors, gaps and imprecisions found in the published arguments during the formalization. Each
entry says where the issue is, what goes wrong, whether the published *result* is affected, and
how the formalization deals with it.

Sources:
* **[AAM]** M. Abrahamsen, A. Adamaszek, T. Miltzow, *The Art Gallery Problem is ∃ℝ-complete*,
  J. ACM 69(1), Article 4 (2021). Numbering below follows the JACM version.
* **[S]** J. Stade, *The Point-Boundary Art Gallery Problem is ∃ℝ-hard*, SoCG 2025
  (LIPIcs 332, Paper 74); full version arXiv:2210.12817v3.

Every entry was checked against the paper text (and, where relevant, its figures) and is given
with a concrete counterexample or argument.

## Summary

| id | source | kind | result affected? |
|---|---|---|---|
| A1 | [AAM] Lemma 21 → Thm 56, Thm 3 (Picasso) | gap in proof | no (statement true; proof needs an extra step) |
| A2 | [AAM] Thm 54, statement | imprecise statement | no (fix: quantify over `[1/2,2]^n`) |
| A3 | [AAM] §5.10–5.11 addition gadgets, pinning of the middle receiver `r_j` | exposition gap (only in the figures) | no |
| A4 | [AAM] §5.8 pockets (Fig. 11) | under-specified | no |
| A5 | [AAM] Lemmas 41/45, nooks in Lemmas 35, 43, 52: sufficiency | exposition gap (critical set seen ⇒ 2-D region seen, asserted) | no |
| A6 | [AAM] §7.2, boundary-guard variant | unsupported remark (the layout of the addition gadgets must change) | no |
| S1 | [S] proof of Thm 2.4 | slip | no |
| S2 | [S] proof of Thm 2.4 | informal reliance on [AAM] internals | no |

## Details

### A1. Lemma 21 does not hold as proved; Theorems 56 and 3 inherit the gap

*Where.* [AAM] §4, Lemma 21 ("alternative stronger version of Lemma 19 for compact
semi-algebraic sets"), used in the proofs of Theorem 56 (§5) and of the Picasso Theorem
(Theorem 3, §6.5).

*Claim.* If an ETR formula `Φ` has a compact solution set `S`, the reduction of Lemma 19, run
with the larger scaling exponent `k := C·L log L + 3` from Basu–Roy (Corollary 20), gives an
ETR-INV instance `Ψ` whose solutions are *exactly* the affine images of the points of `S`, each
extended by auxiliary variables.

*Problem.* The rescaling step needs a bound on *every* variable of the intermediate
`ETR^{1,+,·}` instance, including the auxiliary variables the first step (Lemma 17) adds.
Corollary 20 bounds only the original variables, because only `S` is assumed compact. The
auxiliary variables that encode strict inequalities need not be bounded on `S`: encoding `p > 0`
needs a witness such as `z` with `p·z² = 1`, and `z` blows up as `p → 0`.

*Counterexample.* Take `Φ := 0 ≤ x ≤ 1 ∧ 0 ≤ y ≤ 1 ∧ (x > 0 ∨ x = 0)`, so `S = [0,1]²`, which
is compact. A point `(x, y)` with small `x > 0` satisfies only the branch `x > 0`, whose witness
is about `1/√x`. For any fixed scaling, the points with `x` below some threshold lose all their
witnesses inside `[1/2, 2]`. So the instance represents `S` minus a thin strip, not `S`.

*Effect on the results.* Theorem 3 and Theorem 56 are still true. Every compact (closed)
semi-algebraic set has a description using only `=`, `≤`, `∧`, `∨` (the finiteness theorem for
closed semi-algebraic sets, e.g. Bochnak–Coste–Roy, Thm 2.7.2). For such a description every
auxiliary variable is bounded on `S` (`p ≥ 0` becomes `p = z²` with `|z| = √p`; `∨` becomes a
product), and the paper's argument then goes through. The proof as written omits this step.

*In the formalization.* Theorem 3 (the Picasso theorem) and Theorem 56 are deliberately not
formalized, for three reasons. (i) Their published proof depends on Lemma 21, which fails as
argued; a faithful formal proof of the full statements would need the finiteness theorem for
closed semi-algebraic sets, which is not in Mathlib and would be a substantial development of its
own. (ii) A version restricted to sets described by formulas built from `=`, `≤`, `∧`, `∨` avoids
the gap, but it would be a weaker statement than the paper's and would require two further
gadgets (the Picasso gadget and the scaling gadget of §6) on top of the Section 5 construction.
(iii) Neither theorem is needed for the complexity results: they are universality statements about
the shape of the set of optimal guard positions, not ingredients of the ∃ℝ-completeness proofs.
The coordinate form of this universality is formalized as Theorems 54 and 55 (solutions of an
ETR-INV instance, resp. of any ETR formula, correspond to guard positions in optimal guard sets)
and Theorem 2 (every algebraic number is a forced guard coordinate).

### A2. Theorem 54 is false when read literally (n ≥ 2)

*Where.* [AAM] Theorem 54: "for any `x ∈ ℝⁿ`, `x` is a solution to `Φ` iff there is a guard set
`G` of cardinality `g(Φ)` containing guards at all the positions `(x_1 + d_1, 0), …,
(x_n + d_n, 0)`."

*Problem.* "Containing guards at all the positions" does not require the positions to be
distinct. Let `Φ` be satisfiable with `n ≥ 2`, `G` an optimal guard set, and `u = x̂_1 + d_1`
the guard of variable 1. Put `x_0 := u − d_0` and `x_i := x̂_i` otherwise. Then all positions
`(x_i + d_i, 0)` are in `G` (positions 0 and 1 coincide), but `x_0 ∉ [1/2, 2]`, because
different variables' guard segments are disjoint. So the right-hand side holds while `x` is not
a solution. (Details: `docs/section5/08_proof_plan.md` §0.)

*Effect.* None on the main results: the proof shows the intended statement, with `x` ranging
over `[1/2, 2]ⁿ`.

*In the formalization.* `etrinv_guard_correspondence` requires `x_i ∈ [1/2, 2]` on both sides of
the equivalence.

### A3. The middle receiver of an addition gadget is pinned only in the figures

*Where.* [AAM] §5.10–5.11 (≥- and ≤-addition gadgets; Lemmas 42, 43, 46; Figs. 22–24).

*Observation.* In an addition gadget, three guard families see a common region `Γ`, and each
is joined to the corridor window through its receiver. Since the polygon is simply connected,
the three window–`Γ` paths form a theta graph, and the middle receiver `r_j` lies between two
interior faces. So `r_j` cannot have a local pocket of the kind the paper uses elsewhere (Fig. 6)
to pin a guard to a guard segment (`docs/section5/05_gadgets.md`, "Topological constraint").

*What the paper does.* The text says that "for each guard segment … we introduce pockets of the
polygon, such that the points defining each guard segment … cannot be seen from any other guard
segment or stationary guard position", and the proof of Lemma 42 applies Lemmas 22/23 to "one
point defining each guard segment". For `r_j` the figures (Figs. 22–24) in fact draw *far*
witnesses on the outer boundary:
* a thin spike below `c1` with a horizontal edge at the height of `r_j`;
* a thin slot in the pillar wall (beside `O`), also with a horizontal edge at that height;
* a notch in the lower corridor wall whose side walls lie on the slope-±1 lines through the
  endpoints of `r_j`.
The text never describes these features or checks the conditions of Lemma 23 for them (that no
other guard segment or stationary position sees them, and that their cones meet no other
witness). The checks are routine.

*Effect.* None on the results.

*In the formalization.* The design pins `r_j` with far witnesses of the same kind (`T0`, `T1`
at the height of `r_j`, and two witnesses on lines `x + y = const` fixing its x-range), and the
Lemma 23 conditions are proved explicitly.

### A4. Pockets are under-specified

*Where.* [AAM] §5.8 and Fig. 11 (pockets of the base-line guard segments).

*Problem.* The text fixes some corners and lines and then says "the remaining edges are
constructed so that the points `t0, t1` can be seen only from within the pocket, and that any
point on `s_i` sees the whole pocket". It does not give enough coordinates to check these
visibility claims.

*In the formalization.* Explicit 15–19-vertex pockets with thin witness cones
(`docs/section5/02_main_area.md`). This is an exposition gap, not an error.

### A5. Sufficiency arguments stop at the critical sets

*Where.* [AAM] Lemma 41 (and Lemma 45, "analogous"), and the nook steps in the proofs of
Lemma 35 (Property 3), Lemma 43 (weak-copy nook `Q'_i`; Lemma 46 "in the same way") and Lemma 52
(inversion nook `Q_n`).

*What is omitted.* Definition 24 says only which part of the critical segment `f0f1` each guard
sees ("a guard at p can see all of the segment π_i(p) f_{1−i} but nothing else of f0f1"); nothing in
§5.5–5.6 says that seeing `f0f1` gives the quadrilateral `Q`. The text after Definition 24 argues
only the necessity direction (to see the region bounded by `f0f1` the guards must see `f0f1`).
Lemmas 49 and 50 are stated in the necessity direction only. The converse is then asserted:
"As they can see the complete critical segment for the nook Q^n_σ, they can see all of the polygon
P_σ" (Lemma 35); "Then all of Γ is seen by the guards, as is all of the nook Q'_i" (Lemma 43);
"Then all of Q_u and Q_n is seen by the guards. The remaining area is clearly also seen"
(Lemma 52). In Lemma 41 the paper proves that `g_l` sees the single crossing point `γ` and then
concludes: "Then the guards g_i, g_j, g_l can together see the whole Γ."

*Why it is easy.* For a nook, `p0` sees the part of `Q` on the `f1` side of line `p0c0`, and `p1`
the part on the `f0` side of line `p1c1`. When the traces on `f0f1` meet or overlap, the chords
`c0π0(p0)` and `c1π1(p1)` do not cross inside the convex `Q`, so the two parts cover `Q`. For Γ,
the part not seen by `g_i, g_j` is bounded by the two lines through `γ`; it lies on `g_l`'s side of
line `g_l e_l`, because that line and line `g_j e_j` are both linear in `y` and the required sign
holds at `γ` (by the inequality) and at `y = h`. The coverage of `P_ineq \ Γ` is a separate claim,
asserted with "Observe that…" from the figures: the stationary guards are put on the extreme rays
that bound Γ, so they see up to Γ whatever the values of the guards. Lemma 32 property 2 and
Lemmas 39–40 concern rays and slabs in the corridor, not coverage, so they do not help here.

*Effect.* None. *In the formalization:* the template-coverage proofs use two-dimensional zones (a
triangle below the nook edge, an enlarged Γ) and the same identities with a sign argument
(`Templates/*Cover*.lean`). The ≤-gadget's Γ is enlarged because the formalization restricts the
guards to the value ranges forced by the constraint, which makes the hull of the crossing points
smaller than the paper's Γ. That is a design choice of the formalization, not a gap in the paper.

### A6. The boundary-guard remark of §7.2 does not apply to the addition gadgets as laid out

*Where.* [AAM] §7.2: "It is easy to adjust the construction so that each guard segment is
contained in an edge of the boundary of P. We obtain that the variant of the problem where the
guards are restricted to the boundary is also ∃ℝ-complete."

*Problem.* For the base segments and the corridors this is true (a guard segment can be put on
the floor of a shallow bay). For the addition gadgets it is not, as laid out: the sight lines
that the mechanism and the weak copy need for an open set of values (the strip of `r_i`, the
sight lines from `r_i` to the copy nook, the nook and the sight lines from the nook to `r'_i`,
closed by the mechanism lines from `r'_i`) form a closed curve in the interior of `P` that
encloses the middle receiver `r_j`. Since the interior of a simple polygon is simply connected,
everything inside this curve is interior to `P`, so `r_j` cannot lie on the boundary. In addition,
a guard on a boundary edge sees only one side of the edge, which rules out witnesses on both sides
of a guard segment.

*Effect.* None on the result: the variant is ∃ℝ-complete. A re-laid-out addition gadget (the
receivers exchange their roles; the mechanism of Lemma 41 is unchanged) puts every guard segment
on the outer face, and with bays on all guard segments the construction works
(`docs/boundary_point/design.md`).

### S1. A constant outside the allowed range

*Where.* [S] proof of Theorem 2.4: "we construct variables with values 3/2 and 5/2."

*Problem.* Every ETR-INV-REV variable lies in `[1/2, 2]`, so no variable can equal `5/2`. The
construction never uses that variable: it needs only `1/2` and `3/2`, through `V_1 + V_2 = 3/2`
and `V + 1/2 = V_3`.

*Effect.* None. *In the formalization:* only the constants `1/2` and `3/2` are built
(`ArtGallery/ETR/REV.lean`).

### S2. The interval property is read off from the other paper's proof

*Where.* [S] proof of Theorem 2.4: "Examining the proof of ∃ℝ-hardness of ETR-INV in [2], we
can see that it produces instances … [where] every time a `xy = 1` constraint appears, there is
an interval `I` of length at most 1 such that `x ∈ I` in any satisfying assignment."

*Problem.* [AAM] does not state this property as a lemma; [S] infers it from the construction.
It is true for [AAM]'s reduction (intervals `[8/15, 8/13]`, `[8/7, 8/5]`, `[65/64, 105/64]`), but
it is an informal step.

*In the formalization.* Our ETR → ETR-INV chain proves the property explicitly, with the second
argument of every inversion in `I = [1, 2]` (`Chain.invSystem_complete`), and the REV reduction
uses that (`ArtGallery/ETR/REV.lean`).

## Checked and not an error

* **[AAM] inversion gadget, `f2`.** The coordinates `f2 = (182083/25835, 231222249/19427920)`
  printed in the JACM version are correct (`182083/25835 ≈ 7.05`, matching the paper's own
  approximation).
* **[AAM] Corollary 18** (Schaefer–Štefankovič, quoted in simplified form) is used as a black
  box. This is an external dependency, not an error. The formalization replaces it with an
  elementary self-contained proof of a ball bound of the same strength
  (`ArtGallery/ETR/Ball.lean` and `ArtGallery/ETR/Ball/`).
