module

public import ArtGallery.Vis.API

/-!
# Visibility library: vertex cones (tool T1')

For a simple polygon `P` with the interior to the left of every edge (`P.InteriorLeft`):

* **vertex cone lemma** (`sees_subset_cone`): a point seen from a convex vertex `v` (predecessor
  `u`, successor `w`, `det u v w > 0`) lies in the closed cone `cornerCone u v w`
  (`0 ≤ det u v p` and `0 ≤ det v w p`); consequently the visibility set of `v` lies in the cone
  (`visSet_subset_cone`).  The reflex and straight cases (`sees_vtx_reflex`,
  `sees_vtx_straight`) and the analogue for a point of an open edge (`sees_edge_point`) are also
  given;
* **cone arithmetic**: the decomposition identity `cone_decomp`, a cone lies in a half-plane
  whose value grows along both generators (`det_le_of_mem_cone`), the segment from the apex to a
  cone point lies in the cone (`segment_subset_cone`), and criteria for a segment (a door) to miss
  a cone (`cone_disjoint_segment`, `cone_disjoint_segment_left`, `cone_disjoint_segment_right`).

All conditions are explicit sign conditions on `det`, convenient for parametric families.
-/

@[expose] public section

namespace ArtGallery

namespace Polygon

open Set Filter Topology Metric
open ArtGallery.Geometry (lerp det_lerp lerp_mem_segment)

variable {P : Polygon}

/-! ### Definitions -/

/-- The closed cone at the corner `u → v → w`: the points weakly to the left of both directed
lines `u v` and `v w` (at a convex corner, the interior wedge `v + cone(w − v, u − v)`). -/
def cornerCone (u v w : Point) : Set Point := {x | 0 ≤ det u v x ∧ 0 ≤ det v w x}

/-- The visibility set of `q`: the points of the region seen from `q`. -/
def visSet (P : Polygon) (q : Point) : Set Point := {p | p ∈ P.filled ∧ P.Sees q p}

/-! ### Elementary determinant facts -/

/-- `det a b` along the segment from `b`: `det a b (lerp b p t) = t * det a b p`. -/
theorem det_lerp_from_right (a b p : Point) (t : ℝ) : det a b (lerp b p t) = t * det a b p := by
  unfold det lerp; ring

/-- `det b c` along the segment from `b`: `det b c (lerp b p t) = t * det b c p`. -/
theorem det_lerp_from_left (b c p : Point) (t : ℝ) : det b c (lerp b p t) = t * det b c p := by
  unfold det lerp; ring

/-- Small steps from `v` towards `p` stay in any neighbourhood ball of `v`. -/
theorem exists_lerp_mem_ball (v p : Point) {r : ℝ} (hr : 0 < r) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ dist (lerp v p t) v < r := by
  obtain ⟨t, ⟨ht, ht1⟩, ht0⟩ := (((Jordan.tendsto_lerp_zero v p).eventually
    (isOpen_ball.mem_nhds (mem_ball_self hr))).and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).and
    self_mem_nhdsWithin |>.exists
  exact ⟨t, ht1.1, ht1.2.le, ht⟩

/-! ### The vertex cone lemma -/

/-- **Local wedge at a seen point.** A point `p` seen from vertex `i` satisfies the local wedge
condition at that vertex (the closed wedge at a convex corner, the union of the two closed
half-planes at a reflex corner, the closed half-plane at a straight corner). -/
theorem sees_vtx_wedge (hP : P.Simple) (hL : P.InteriorLeft) {i : ℕ} (hi : i < P.n)
    {p : Point} (h : P.Sees (P.vtx i) p) :
    Vis.wedgeCond (P.vtx ((i + P.n - 1) % P.n)) (P.vtx i) (P.vtx ((i + 1) % P.n)) p := by
  obtain ⟨r, hr, hloc⟩ := Vis.local_wedge hP hL hi
  unfold Jordan.prevIdx at hloc
  obtain ⟨t, ht0, ht1, hd⟩ := exists_lerp_mem_ball (P.vtx i) p hr
  have hz := (hloc _ hd).1 (h (lerp_mem_segment _ _ ht0.le ht1))
  unfold Vis.wedgeCond Vis.condR at hz ⊢
  rw [det_lerp_from_right, det_lerp_from_left] at hz
  have key : ∀ A : ℝ, 0 ≤ t * A → 0 ≤ A := fun A hA => (mul_nonneg_iff_of_pos_left ht0).1 hA
  split_ifs at hz ⊢
  · exact ⟨key _ hz.1, key _ hz.2⟩
  · exact hz.imp (key _) (key _)
  · exact key _ hz

/-- **Vertex cone lemma (T1').** Let `v = P.vtx i` be a convex vertex with predecessor `u` and
successor `w` (`det u v w > 0`).  Every point `p` seen from `v` lies in the closed cone at `v`:
`0 ≤ det u v p` and `0 ≤ det v w p`. -/
theorem sees_subset_cone (hP : P.Simple) (hL : P.InteriorLeft) {i : ℕ} (hi : i < P.n)
    {u v w : Point} (hu : P.vtx ((i + P.n - 1) % P.n) = u) (hv : P.vtx i = v)
    (hw : P.vtx ((i + 1) % P.n) = w) (hconv : 0 < det u v w) {p : Point}
    (h : P.Sees v p) : 0 ≤ det u v p ∧ 0 ≤ det v w p := by
  subst hu hv hw
  have hc := sees_vtx_wedge hP hL hi h
  unfold Vis.wedgeCond Vis.condR at hc
  rwa [ite_eq_left hconv] at hc

/-- The vertex cone lemma with the seeing relation in the other direction. -/
theorem sees_subset_cone' (hP : P.Simple) (hL : P.InteriorLeft) {i : ℕ} (hi : i < P.n)
    {u v w : Point} (hu : P.vtx ((i + P.n - 1) % P.n) = u) (hv : P.vtx i = v)
    (hw : P.vtx ((i + 1) % P.n) = w) (hconv : 0 < det u v w) {p : Point}
    (h : P.Sees p v) : 0 ≤ det u v p ∧ 0 ≤ det v w p :=
  sees_subset_cone hP hL hi hu hv hw hconv (sees_comm.1 h)

/-- **Witness cone.** The visibility set of a convex vertex lies in its cone. -/
theorem visSet_subset_cone (hP : P.Simple) (hL : P.InteriorLeft) {i : ℕ} (hi : i < P.n)
    {u v w : Point} (hu : P.vtx ((i + P.n - 1) % P.n) = u) (hv : P.vtx i = v)
    (hw : P.vtx ((i + 1) % P.n) = w) (hconv : 0 < det u v w) :
    P.visSet v ⊆ cornerCone u v w :=
  fun _ hp => sees_subset_cone hP hL hi hu hv hw hconv hp.2

/-- The vertex cone lemma at a reflex vertex (`det u v w < 0`): a seen point is weakly to the
left of one of the two incident edges. -/
theorem sees_vtx_reflex (hP : P.Simple) (hL : P.InteriorLeft) {i : ℕ} (hi : i < P.n)
    {u v w : Point} (hu : P.vtx ((i + P.n - 1) % P.n) = u) (hv : P.vtx i = v)
    (hw : P.vtx ((i + 1) % P.n) = w) (hrefl : det u v w < 0) {p : Point}
    (h : P.Sees v p) : 0 ≤ det u v p ∨ 0 ≤ det v w p := by
  subst hu hv hw
  have hc := sees_vtx_wedge hP hL hi h
  unfold Vis.wedgeCond Vis.condR at hc
  rwa [ite_eq_right (not_lt.2 hrefl.le), ite_eq_left hrefl] at hc

/-- The vertex cone lemma at a straight vertex (`det u v w = 0`): a seen point is weakly to the
left of the incoming edge. -/
theorem sees_vtx_straight (hP : P.Simple) (hL : P.InteriorLeft) {i : ℕ} (hi : i < P.n)
    {u v w : Point} (hu : P.vtx ((i + P.n - 1) % P.n) = u) (hv : P.vtx i = v)
    (hw : P.vtx ((i + 1) % P.n) = w) (hstr : det u v w = 0) {p : Point}
    (h : P.Sees v p) : 0 ≤ det u v p := by
  subst hu hv hw
  have hc := sees_vtx_wedge hP hL hi h
  unfold Vis.wedgeCond Vis.condR at hc
  rwa [hstr, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _)] at hc

/-- **Half-plane at an edge point.** A point seen from a point `y` of the open edge `i` is weakly
to the left of the edge. -/
theorem sees_edge_point (hP : P.Simple) (hL : P.InteriorLeft) {i : ℕ} (hi : i < P.n)
    {a b : Point} (ha : P.vtx i = a) (hb : P.vtx ((i + 1) % P.n) = b) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) {p : Point} (h : P.Sees (lerp a b t) p) : 0 ≤ det a b p := by
  subst ha hb
  obtain ⟨r, hr, hloc⟩ := local_halfplane hP hL hi ht0 ht1
  rw [← Geometry.lerp_eq_add_smul] at hloc
  obtain ⟨s, hs0, hs1, hd⟩ := exists_lerp_mem_ball (lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t) p hr
  have hz := (hloc _ hd).1 (h (lerp_mem_segment _ _ hs0.le hs1))
  rw [det_lerp, Geometry.det_lerp_self, mul_zero, zero_add] at hz
  exact (mul_nonneg_iff_of_pos_left hs0).1 hz

/-! ### Cone arithmetic -/

/-- **Cone decomposition.** With `D = det u v w`, `A = det u v x`, `B = det v w x`:
`D • (x − v) = A • (w − v) + B • (u − v)`, read through an arbitrary affine function
`det c d`. -/
theorem cone_decomp (u v w c d x : Point) :
    det u v w * (det c d x - det c d v) =
      det u v x * (det c d w - det c d v) + det v w x * (det c d u - det c d v) := by
  unfold det; ring

/-- **A cone lies in a half-plane** whose defining affine function `det c d` does not decrease
along the two generators `w − v` and `u − v` of the cone at a convex corner. -/
theorem det_le_of_mem_cone {u v w c d x : Point} (hD : 0 < det u v w)
    (hx : x ∈ cornerCone u v w) (hu : det c d v ≤ det c d u) (hw : det c d v ≤ det c d w) :
    det c d v ≤ det c d x := by
  have e := cone_decomp u v w c d x
  have h1 : 0 ≤ det u v x * (det c d w - det c d v) := mul_nonneg hx.1 (by linarith)
  have h2 : 0 ≤ det v w x * (det c d u - det c d v) := mul_nonneg hx.2 (by linarith)
  have h3 : 0 ≤ det u v w * (det c d x - det c d v) := by linarith
  have := (mul_nonneg_iff_of_pos_left hD).1 h3
  linarith

/-- A cone at a convex corner lies in the closed half-plane `0 ≤ det c d ·` when the apex is on
the line `c d` (`det c d v = 0`) and both neighbours `u, w` are weakly on its left. -/
theorem det_nonneg_of_mem_cone {u v w c d x : Point} (hD : 0 < det u v w)
    (hx : x ∈ cornerCone u v w) (hv : det c d v = 0) (hu : 0 ≤ det c d u) (hw : 0 ≤ det c d w) :
    0 ≤ det c d x := by
  have := det_le_of_mem_cone hD hx (c := c) (d := d) (by linarith) (by linarith)
  linarith

/-- Coordinates of the cone decomposition: `D • (x − v) = A • (w − v) + B • (u − v)` with
`D = det u v w`, `A = det u v x`, `B = det v w x`. -/
theorem cone_decomp_coord (u v w x : Point) :
    det u v w * (x.1 - v.1) = det u v x * (w.1 - v.1) + det v w x * (u.1 - v.1) ∧
      det u v w * (x.2 - v.2) = det u v x * (w.2 - v.2) + det v w x * (u.2 - v.2) := by
  constructor <;> (unfold det; ring)

/-- **Strict half-plane containing a cone.** If the line `c d` passes through the apex `v` of the
cone at the convex corner `u v w` and both neighbours `u, w` are strictly on its left, every
point of the cone other than `v` is strictly on its left. -/
theorem det_pos_of_mem_cone {u v w c d x : Point} (hD : 0 < det u v w)
    (hx : x ∈ cornerCone u v w) (hxv : x ≠ v) (hv : det c d v = 0) (hu : 0 < det c d u)
    (hw : 0 < det c d w) : 0 < det c d x := by
  by_contra hneg
  have hle : det c d x ≤ 0 := not_lt.1 hneg
  have e := cone_decomp u v w c d x
  rw [hv, sub_zero, sub_zero, sub_zero] at e
  have h1 : 0 ≤ det u v x * det c d w := mul_nonneg hx.1 hw.le
  have h2 : 0 ≤ det v w x * det c d u := mul_nonneg hx.2 hu.le
  have h3 : det u v w * det c d x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hD.le hle
  have hA : det u v x = 0 := by
    by_contra hA
    have : 0 < det u v x * det c d w := mul_pos (lt_of_le_of_ne hx.1 (Ne.symm hA)) hw
    linarith
  have hB : det v w x = 0 := by
    by_contra hB
    have : 0 < det v w x * det c d u := mul_pos (lt_of_le_of_ne hx.2 (Ne.symm hB)) hu
    linarith
  obtain ⟨d1, d2⟩ := cone_decomp_coord u v w x
  rw [hA, hB] at d1 d2
  have g1 : x.1 - v.1 = 0 := by
    rcases mul_eq_zero.1 (show det u v w * (x.1 - v.1) = 0 by rw [d1]; ring) with h | h
    · exact absurd h hD.ne'
    · exact h
  have g2 : x.2 - v.2 = 0 := by
    rcases mul_eq_zero.1 (show det u v w * (x.2 - v.2) = 0 by rw [d2]; ring) with h | h
    · exact absurd h hD.ne'
    · exact h
  exact hxv (Prod.ext (by linarith) (by linarith))

/-- The cone at a corner contains the segment from its apex to any of its points. -/
theorem segment_subset_cone {u v w x : Point} (hx : x ∈ cornerCone u v w) :
    ArtGallery.segment v x ⊆ cornerCone u v w := by
  rintro y ⟨t, ht0, ht1, rfl⟩
  have e : (v.1 + t * (x.1 - v.1), v.2 + t * (x.2 - v.2)) = lerp v x t := rfl
  rw [e]
  exact ⟨by rw [det_lerp_from_right]; exact mul_nonneg ht0 hx.1,
    by rw [det_lerp_from_left]; exact mul_nonneg ht0 hx.2⟩

/-- An affine function `det c d` negative at both endpoints of a segment is negative on it. -/
theorem det_neg_of_mem_segment {c d a b y : Point} (ha : det c d a < 0) (hb : det c d b < 0)
    (hy : y ∈ ArtGallery.segment a b) : det c d y < 0 := by
  obtain ⟨t, ht0, ht1, rfl⟩ := hy
  have e : (a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2)) = lerp a b t := rfl
  rw [e, det_lerp]
  nlinarith [mul_nonneg ht0 (neg_nonneg.2 hb.le), mul_nonneg (sub_nonneg.2 ht1) (neg_nonneg.2 ha.le)]

/-- **A door missing a cone (separating line).** If the affine function `det c d` does not
decrease from the apex `v` along both generators of the cone at the convex corner `u v w`, and is
strictly smaller than at `v` at both endpoints of the segment `a b`, the segment misses the cone. -/
theorem cone_disjoint_segment {u v w c d a b : Point} (hD : 0 < det u v w)
    (hu : det c d v ≤ det c d u) (hw : det c d v ≤ det c d w) (ha : det c d a < det c d v)
    (hb : det c d b < det c d v) : ∀ y ∈ ArtGallery.segment a b, y ∉ cornerCone u v w := by
  intro y hy hyc
  have h1 := det_le_of_mem_cone hD hyc hu hw
  obtain ⟨t, ht0, ht1, rfl⟩ := hy
  have e : (a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2)) = lerp a b t := rfl
  rw [e, det_lerp] at h1
  nlinarith [mul_nonneg ht0 (sub_nonneg.2 hb.le), mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 ha.le)]

/-- A segment with both endpoints strictly to the right of the outgoing edge line `v w` misses
the cone at `u v w`. -/
theorem cone_disjoint_segment_left {u v w a b : Point} (ha : det v w a < 0) (hb : det v w b < 0) :
    ∀ y ∈ ArtGallery.segment a b, y ∉ cornerCone u v w :=
  fun _ hy hyc => absurd hyc.2 (not_le.2 (det_neg_of_mem_segment ha hb hy))

/-- A segment with both endpoints strictly to the right of the incoming edge line `u v` misses
the cone at `u v w`. -/
theorem cone_disjoint_segment_right {u v w a b : Point} (ha : det u v a < 0)
    (hb : det u v b < 0) : ∀ y ∈ ArtGallery.segment a b, y ∉ cornerCone u v w :=
  fun _ hy hyc => absurd hyc.1 (not_le.2 (det_neg_of_mem_segment ha hb hy))

/-- **Disjoint visibility from disjoint cones.** If the cones of two convex vertices are
disjoint, no point sees both vertices. -/
theorem not_sees_both_of_cones_disjoint (hP : P.Simple) (hL : P.InteriorLeft) {i j : ℕ}
    (hi : i < P.n) (hj : j < P.n) {u v w u' v' w' : Point}
    (hu : P.vtx ((i + P.n - 1) % P.n) = u) (hv : P.vtx i = v) (hw : P.vtx ((i + 1) % P.n) = w)
    (hconv : 0 < det u v w) (hu' : P.vtx ((j + P.n - 1) % P.n) = u') (hv' : P.vtx j = v')
    (hw' : P.vtx ((j + 1) % P.n) = w') (hconv' : 0 < det u' v' w')
    (hdisj : ∀ x, x ∈ cornerCone u v w → x ∉ cornerCone u' v' w') {p : Point}
    (h : P.Sees p v) : ¬ P.Sees p v' := fun h' =>
  hdisj p (sees_subset_cone' hP hL hi hu hv hw hconv h)
    (sees_subset_cone' hP hL hj hu' hv' hw' hconv' h')

end Polygon

end ArtGallery

end
