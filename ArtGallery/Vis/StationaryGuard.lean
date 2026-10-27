module

public import ArtGallery.Vis.Cones

/-!
# Visibility library: the stationary-guard lemma

Let `p` be a vertex of a simple polygon with incident edges `u → p` and `p → w`, and let `qa, qb`
be two points (the tips of two slots) strictly inside the wedge at `p`, with `qb`
counter-clockwise from `qa` as seen from `p` (`det p qa qb > 0`).  Suppose every point seeing `qa`
lies weakly to the right of the directed line `p → qa`, and every point seeing `qb` weakly to the
left of `p → qb` (the line through `p` bounds the cone of each tip, the cone of `qa` on the side of
the edge `p → w`, that of `qb` on the side of `u → p`).  If moreover every point seeing both tips
is strictly to the right of the line `qa → w` and strictly to the left of the line `qb → u`
(the far-side conditions), then **the only point seeing both tips is `p`**
(`sg_unique_gen`).

Proof.  Write `K = det p qa qb` and `x − p = −α (qa − p) − β (qb − p)`; the cone conditions give
`α, β ≥ 0`.  If `β > 0` the segment `x qa` properly crosses the edge `p w`, if `α > 0` the
segment `x qb` properly crosses the edge `u p` (explicit sign computations, blocking lemma T1);
if `α = β = 0` then `x = p`.

Two ways to discharge the far-side conditions:
* `sg_unique`: from the "reach" inequalities `det p qa qb ≤ det p w qb`, `det p qa qb ≤ det u p qa`
  (only the half-plane parts of the cones are used; this needs long edges at `p`);
* `sg_unique_of_vertices`: the tips are convex vertices of `P` and the explicit cones at the tips
  (vertex cone lemma) are used: conditions on the neighbours `ua, wa` of `qa` and `ub, wb` of `qb`
  (`0 ≤ det qa p ua`, `0 ≤ det qa p wa`, `det qa w ua < 0`, `det qa w wa < 0`,
  `0 ≤ det p qb ub`, `0 ≤ det p qb wb`, `0 < det qb u ub`, `0 < det qb u wb`).  This is the form
  that applies to the thin slot cones of the construction.
-/

@[expose] public section

namespace ArtGallery

namespace Polygon

variable {P : Polygon}

/-- The coordinate identity behind the stationary-guard lemma:
`det p qa qb • (x − p) = −det p qb x • (qa − p) + det p qa x • (qb − p)`. -/
theorem sg_decomp (p qa qb x : Point) :
    det p qa qb * (x.1 - p.1) = -(det p qb x) * (qa.1 - p.1) + det p qa x * (qb.1 - p.1) ∧
      det p qa qb * (x.2 - p.2) = -(det p qb x) * (qa.2 - p.2) + det p qa x * (qb.2 - p.2) := by
  constructor <;> (unfold det; ring)

/-- **Stationary-guard lemma, general form.** Let `u → p` (edge `j₀`) and `p → w` (edge `j₁`) be
the two edges at the vertex `p`, and let `qa, qb` satisfy
* `0 < det p w qa`, `0 < det p w qb`, `0 < det u p qa`, `0 < det u p qb` (both tips strictly on
  the inner sides of both edges),
* `0 < det p qa qb` (`qb` is counter-clockwise from `qa` around `p`),
* every point seeing `qa` satisfies `det p qa x ≤ 0`, every point seeing `qb` satisfies
  `0 ≤ det p qb x` (cone conditions),
* every point seeing both satisfies `det qa w x < 0` and `0 < det qb u x` (far-side conditions).

Then every point seeing both `qa` and `qb` is `p`. -/
theorem sg_unique_gen (hP : P.Simple) {j₀ j₁ : ℕ} (hj₀ : j₀ < P.n) (hj₁ : j₁ < P.n)
    {u p w qa qb : Point} (hu : P.vtx j₀ = u) (hp₀ : P.vtx ((j₀ + 1) % P.n) = p)
    (hp₁ : P.vtx j₁ = p) (hw : P.vtx ((j₁ + 1) % P.n) = w)
    (hwa : 0 < det p w qa) (hwb : 0 < det p w qb) (hua : 0 < det u p qa) (hub : 0 < det u p qb)
    (hab : 0 < det p qa qb)
    (hconeA : ∀ x, P.Sees x qa → det p qa x ≤ 0) (hconeB : ∀ x, P.Sees x qb → 0 ≤ det p qb x)
    (hfarW : ∀ x, P.Sees x qa → P.Sees x qb → det qa w x < 0)
    (hfarU : ∀ x, P.Sees x qa → P.Sees x qb → 0 < det qb u x)
    {x : Point} (hxa : P.Sees x qa) (hxb : P.Sees x qb) : x = p := by
  set K := det p qa qb with hK
  have hA := hconeA x hxa
  have hB := hconeB x hxb
  rcases hA.lt_or_eq with hA' | hA'
  · -- the segment `x qa` properly crosses the edge `p w`
    exfalso
    have e1 : K * det p w x = -(det p qb x) * det p w qa + det p qa x * det p w qb := by
      rw [hK]; unfold det; ring
    have e3 : det x qa p = -det p qa x := by unfold det; ring
    have e4 : det x qa w = det qa w x := by unfold det; ring
    have hwx : det p w x < 0 := by
      have : K * det p w x < 0 := by
        rw [e1]
        nlinarith [mul_nonneg hB hwa.le, mul_pos (neg_pos.2 hA') hwb]
      by_contra h
      nlinarith [mul_nonneg hab.le (not_lt.1 h)]
    have hxw : det x qa w < 0 := by rw [e4]; exact hfarW x hxa hxb
    refine not_sees_of_proper_cross hP hj₁ (p := x) (q := qa) ?_ ?_ hxa
    · rw [hp₁, hw]
      nlinarith [mul_pos (neg_pos.2 hwx) hwa]
    · rw [hp₁, hw, e3]
      nlinarith [mul_pos (neg_pos.2 hA') (neg_pos.2 hxw)]
  rcases hB.lt_or_eq with hB' | hB'
  · -- the segment `x qb` properly crosses the edge `u p`
    exfalso
    have e1 : K * det u p x = -(det p qb x) * det u p qa + det p qa x * det u p qb := by
      rw [hK]; unfold det; ring
    have e3 : det x qb p = -det p qb x := by unfold det; ring
    have e4 : det x qb u = det qb u x := by unfold det; ring
    have hux : det u p x < 0 := by
      have : K * det u p x < 0 := by
        rw [e1, ← hA']
        nlinarith [mul_pos hB' hua]
      by_contra h
      nlinarith [mul_nonneg hab.le (not_lt.1 h)]
    have hxu : 0 < det x qb u := by rw [e4]; exact hfarU x hxa hxb
    refine not_sees_of_proper_cross hP hj₀ (p := x) (q := qb) ?_ ?_ hxb
    · rw [hu, hp₀]
      nlinarith [mul_pos (neg_pos.2 hux) hub]
    · rw [hu, hp₀, e3]
      nlinarith [mul_pos hxu hB']
  · -- both coordinates vanish
    obtain ⟨d1, d2⟩ := sg_decomp p qa qb x
    have h1 : K * (x.1 - p.1) = 0 := by rw [hK, d1, hA', ← hB']; ring
    have h2 : K * (x.2 - p.2) = 0 := by rw [hK, d2, hA', ← hB']; ring
    have hK0 : K ≠ 0 := hab.ne'
    have g1 := (mul_eq_zero.1 h1).resolve_left hK0
    have g2 := (mul_eq_zero.1 h2).resolve_left hK0
    exact Prod.ext (by linarith) (by linarith)

/-- **Stationary-guard lemma, half-plane form.** As `sg_unique_gen`, with the far-side
conditions replaced by the reach inequalities `det p qa qb ≤ det p w qb` and
`det p qa qb ≤ det u p qa` (the edges at `p` are long compared with the tips). -/
theorem sg_unique (hP : P.Simple) {j₀ j₁ : ℕ} (hj₀ : j₀ < P.n) (hj₁ : j₁ < P.n)
    {u p w qa qb : Point} (hu : P.vtx j₀ = u) (hp₀ : P.vtx ((j₀ + 1) % P.n) = p)
    (hp₁ : P.vtx j₁ = p) (hw : P.vtx ((j₁ + 1) % P.n) = w)
    (hwa : 0 < det p w qa) (hub : 0 < det u p qb) (hab : 0 < det p qa qb)
    (hKw : det p qa qb ≤ det p w qb) (hKu : det p qa qb ≤ det u p qa)
    (hconeA : ∀ x, P.Sees x qa → det p qa x ≤ 0) (hconeB : ∀ x, P.Sees x qb → 0 ≤ det p qb x)
    {x : Point} (hxa : P.Sees x qa) (hxb : P.Sees x qb) : x = p := by
  have hwb : 0 < det p w qb := lt_of_lt_of_le hab hKw
  have hua : 0 < det u p qa := lt_of_lt_of_le hab hKu
  refine sg_unique_gen hP hj₀ hj₁ hu hp₀ hp₁ hw hwa hwb hua hub hab hconeA hconeB
    (fun y hya hyb => ?_) (fun y hya hyb => ?_) hxa hxb
  · have hA := hconeA y hya
    have hB := hconeB y hyb
    have e2 : det p qa qb * det qa w y = -(det p qa qb * det p w qa) +
        det p qa y * (det p w qb - det p qa qb) - det p qb y * det p w qa := by
      unfold det; ring
    have : det p qa qb * det qa w y < 0 := by
      rw [e2]
      nlinarith [mul_pos hab hwa, mul_nonneg (neg_nonneg.2 hA) (sub_nonneg.2 hKw),
        mul_nonneg hB hwa.le]
    by_contra h
    nlinarith [mul_nonneg hab.le (not_lt.1 h)]
  · have hA := hconeA y hya
    have hB := hconeB y hyb
    have e2 : det p qa qb * det qb u y = det p qa qb * det u p qb +
        det p qb y * (det u p qa - det p qa qb) - det p qa y * det u p qb := by
      unfold det; ring
    have : 0 < det p qa qb * det qb u y := by
      rw [e2]
      nlinarith [mul_pos hab hub, mul_nonneg hB (sub_nonneg.2 hKu),
        mul_nonneg (neg_nonneg.2 hA) hub.le]
    by_contra h
    nlinarith [mul_nonneg hab.le (neg_nonneg.2 (not_lt.1 h))]

/-- **Stationary-guard lemma for vertex tips (thin cones).** As `sg_unique_gen`, with the cone
and far-side conditions derived from the vertex cone lemma: `qa = P.vtx ia` is a convex vertex
(predecessor `ua`, successor `wa`) and `qb = P.vtx ib` is a convex vertex (predecessor `ub`,
successor `wb`) such that
* the cone of `qa` lies weakly right of `p → qa`: `0 ≤ det qa p ua`, `0 ≤ det qa p wa`;
* the cone of `qb` lies weakly left of `p → qb`: `0 ≤ det p qb ub`, `0 ≤ det p qb wb`;
* the cone of `qa` lies strictly right of `qa → w`: `det qa w ua < 0`, `det qa w wa < 0`;
* the cone of `qb` lies strictly left of `qb → u`: `0 < det qb u ub`, `0 < det qb u wb`.

Then every point seeing both `qa` and `qb` is `p`. -/
theorem sg_unique_of_vertices (hP : P.Simple) (hL : P.InteriorLeft) {j₀ j₁ ia ib : ℕ}
    (hj₀ : j₀ < P.n) (hj₁ : j₁ < P.n) (hia : ia < P.n) (hib : ib < P.n)
    {u p w qa qb ua wa ub wb : Point} (hu : P.vtx j₀ = u) (hp₀ : P.vtx ((j₀ + 1) % P.n) = p)
    (hp₁ : P.vtx j₁ = p) (hw : P.vtx ((j₁ + 1) % P.n) = w)
    (hua' : P.vtx ((ia + P.n - 1) % P.n) = ua) (hqa : P.vtx ia = qa)
    (hwa' : P.vtx ((ia + 1) % P.n) = wa) (hconva : 0 < det ua qa wa)
    (hub' : P.vtx ((ib + P.n - 1) % P.n) = ub) (hqb : P.vtx ib = qb)
    (hwb' : P.vtx ((ib + 1) % P.n) = wb) (hconvb : 0 < det ub qb wb)
    (hwa : 0 < det p w qa) (hwb : 0 < det p w qb) (hua : 0 < det u p qa) (hub : 0 < det u p qb)
    (hab : 0 < det p qa qb)
    (hconeA₁ : 0 ≤ det qa p ua) (hconeA₂ : 0 ≤ det qa p wa)
    (hconeB₁ : 0 ≤ det p qb ub) (hconeB₂ : 0 ≤ det p qb wb)
    (hfarA₁ : det qa w ua < 0) (hfarA₂ : det qa w wa < 0)
    (hfarB₁ : 0 < det qb u ub) (hfarB₂ : 0 < det qb u wb)
    {x : Point} (hxa : P.Sees x qa) (hxb : P.Sees x qb) : x = p := by
  have hcA : ∀ y, P.Sees y qa → y ∈ cornerCone ua qa wa :=
    fun y hy => sees_subset_cone' hP hL hia hua' hqa hwa' hconva hy
  have hcB : ∀ y, P.Sees y qb → y ∈ cornerCone ub qb wb :=
    fun y hy => sees_subset_cone' hP hL hib hub' hqb hwb' hconvb hy
  have hconeA : ∀ y, P.Sees y qa → det p qa y ≤ 0 := by
    intro y hy
    have := det_nonneg_of_mem_cone hconva (hcA y hy) (Geometry.det_self_outer qa p) hconeA₁
      hconeA₂
    have e : det p qa y = -det qa p y := by unfold det; ring
    linarith
  have hconeB : ∀ y, P.Sees y qb → 0 ≤ det p qb y := fun y hy =>
    det_nonneg_of_mem_cone hconvb (hcB y hy) (Geometry.det_self_right p qb) hconeB₁ hconeB₂
  refine sg_unique_gen hP hj₀ hj₁ hu hp₀ hp₁ hw hwa hwb hua hub hab hconeA hconeB
    (fun y hya hyb => ?_) (fun y hya hyb => ?_) hxa hxb
  · -- `y ≠ qa`, since `qa` is strictly right of `p → qb`
    have hyqa : y ≠ qa := by
      rintro rfl
      have h := hconeB y hyb
      have e : det p qb y = -det p y qb := by unfold det; ring
      linarith
    have := det_pos_of_mem_cone (c := w) (d := qa) hconva (hcA y hya) hyqa
      (Geometry.det_self_right w qa)
      (by have e : det w qa ua = -det qa w ua := by unfold det; ring
          linarith)
      (by have e : det w qa wa = -det qa w wa := by unfold det; ring
          linarith)
    have e : det qa w y = -det w qa y := by unfold det; ring
    linarith
  · -- `y ≠ qb`, since `qb` is strictly left of `p → qa`
    have hyqb : y ≠ qb := by
      rintro rfl
      have h := hconeA y hya
      linarith
    exact det_pos_of_mem_cone hconvb (hcB y hyb) hyqb (Geometry.det_self_outer qb u) hfarB₁
      hfarB₂

end Polygon

end ArtGallery

end
