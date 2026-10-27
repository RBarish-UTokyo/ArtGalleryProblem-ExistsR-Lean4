module

public import ArtGallery.Geometry.Det

/-!
# Triangles

A triangle is `convexHull ℝ {a, b, c}`.  This file provides

* the three-weight description of the hull (`mem_convexHull_triple`), valid for any `a b c`;
* barycentric coordinates `bary₁ bary₂ bary₃` for a nondegenerate triangle
  (`det a b c ≠ 0`), their sum, reconstruction, uniqueness, continuity, affinity along
  segments and values at the vertices;
* `mem_triangle_iff_bary` and the description of the interior `interior_triangle`;
* nonemptiness of the interior (`centroid_mem_interior`), compactness, closedness,
  boundedness and convexity of a triangle;
* the three edges as faces (`mem_segment_iff_bary₃_eq_zero`, …);
* the link with the specification's `Polygon.triSet`, `Polygon.triVertices`,
  `Polygon.validTriangle`.

Provenance: adapted from `Chazelle/Geometry/Triangle.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery`.
-/

namespace ArtGallery

namespace Geometry

open Topology

@[expose] public section

/-! ### Convex combinations of three points -/

/-- The vertices lie in the triangle. -/
theorem vertex_mem_triangle_left (a b c : Point) : a ∈ convexHull ℝ ({a, b, c} : Set Point) :=
  subset_convexHull ℝ _ (by simp)

theorem vertex_mem_triangle_mid (a b c : Point) : b ∈ convexHull ℝ ({a, b, c} : Set Point) :=
  subset_convexHull ℝ _ (by simp)

theorem vertex_mem_triangle_right (a b c : Point) : c ∈ convexHull ℝ ({a, b, c} : Set Point) :=
  subset_convexHull ℝ _ (by simp)

/-- A point of `convexHull ℝ {a, b, c}` is a convex combination of `a`, `b`, `c`
(no nondegeneracy needed). -/
theorem mem_convexHull_triple {a b c x : Point} :
    x ∈ convexHull ℝ ({a, b, c} : Set Point) ↔
      ∃ w₁ w₂ w₃ : ℝ, 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ 0 ≤ w₃ ∧ w₁ + w₂ + w₃ = 1 ∧
        x = w₁ • a + w₂ • b + w₃ • c := by
  constructor
  · intro hx
    -- the set of convex combinations is convex and contains the three points
    suffices hS : convexHull ℝ ({a, b, c} : Set Point) ⊆
        {y : Point | ∃ w₁ w₂ w₃ : ℝ, 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ 0 ≤ w₃ ∧ w₁ + w₂ + w₃ = 1 ∧
          y = w₁ • a + w₂ • b + w₃ • c} from hS hx
    refine convexHull_min ?_ ?_
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨1, 0, 0, zero_le_one, le_rfl, le_rfl, by norm_num, by simp⟩
      · exact ⟨0, 1, 0, le_rfl, zero_le_one, le_rfl, by norm_num, by simp⟩
      · exact ⟨0, 0, 1, le_rfl, le_rfl, zero_le_one, by norm_num, by simp⟩
    · rintro y ⟨u₁, u₂, u₃, hu₁, hu₂, hu₃, hu, rfl⟩ z ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, hv, rfl⟩
        s t hs ht hst
      refine ⟨s * u₁ + t * v₁, s * u₂ + t * v₂, s * u₃ + t * v₃, by positivity, by positivity,
        by positivity, by linear_combination s * hu + t * hv + hst, ?_⟩
      ext <;> simp only [add_fst, add_snd, smul_fst, smul_snd] <;> ring
  · rintro ⟨w₁, w₂, w₃, hw₁, hw₂, hw₃, hw, rfl⟩
    have h := (convex_convexHull ℝ ({a, b, c} : Set Point)).sum_mem (t := Finset.univ)
      (w := ![w₁, w₂, w₃]) (z := ![a, b, c]) ?_ ?_ ?_
    · simpa [Fin.sum_univ_three] using h
    · intro i _
      fin_cases i <;> simp [hw₁, hw₂, hw₃]
    · simp [Fin.sum_univ_three, hw]
    · intro i _
      fin_cases i <;> simp [vertex_mem_triangle_left, vertex_mem_triangle_mid,
        vertex_mem_triangle_right]

/-! ### Barycentric coordinates -/

/-- First barycentric coordinate of `x` with respect to the triangle `a b c`. -/
noncomputable def bary₁ (a b c x : Point) : ℝ := det x b c / det a b c

/-- Second barycentric coordinate of `x` with respect to the triangle `a b c`. -/
noncomputable def bary₂ (a b c x : Point) : ℝ := det a x c / det a b c

/-- Third barycentric coordinate of `x` with respect to the triangle `a b c`. -/
noncomputable def bary₃ (a b c x : Point) : ℝ := det a b x / det a b c

/-- The barycentric coordinates sum to `1`. -/
theorem bary_sum {a b c : Point} (h : det a b c ≠ 0) (x : Point) :
    bary₁ a b c x + bary₂ a b c x + bary₃ a b c x = 1 := by
  unfold bary₁ bary₂ bary₃
  rw [← add_div, ← add_div, det_bary_sum, div_self h]

/-- The barycentric reconstruction: `x = bary₁ • a + bary₂ • b + bary₃ • c`. -/
theorem bary_reconstruct {a b c : Point} (h : det a b c ≠ 0) (x : Point) :
    x = bary₁ a b c x • a + bary₂ a b c x • b + bary₃ a b c x • c := by
  have hid := det_smul_eq_bary_combination a b c x
  rw [point_ext_iff] at hid ⊢
  simp only [add_fst, add_snd, smul_fst, smul_snd] at hid ⊢
  unfold bary₁ bary₂ bary₃
  constructor
  · field_simp; linear_combination hid.1
  · field_simp; linear_combination hid.2

/-- Uniqueness of barycentric coordinates: the third coordinate of
`w₁ • a + w₂ • b + w₃ • c` (weights summing to `1`) is `w₃`. -/
theorem bary₃_combination {a b c : Point} (h : det a b c ≠ 0) {w₁ w₂ w₃ : ℝ}
    (hw : w₁ + w₂ + w₃ = 1) : bary₃ a b c (w₁ • a + w₂ • b + w₃ • c) = w₃ := by
  unfold bary₃
  rw [det_smul_add_smul_add_smul a b a b c w₁ w₂ w₃ hw]
  simp only [det_self_outer, det_self_right, mul_zero, zero_add]
  exact mul_div_cancel_right₀ _ h

/-- The first barycentric coordinate of `w₁ • a + w₂ • b + w₃ • c` is `w₁`. -/
theorem bary₁_combination {a b c : Point} (h : det a b c ≠ 0) {w₁ w₂ w₃ : ℝ}
    (hw : w₁ + w₂ + w₃ = 1) : bary₁ a b c (w₁ • a + w₂ • b + w₃ • c) = w₁ := by
  unfold bary₁
  rw [← det_cyclic, det_smul_add_smul_add_smul b c a b c w₁ w₂ w₃ hw]
  simp only [det_self_outer, det_self_right, mul_zero, add_zero, det_cyclic]
  exact mul_div_cancel_right₀ _ h

/-- The second barycentric coordinate of `w₁ • a + w₂ • b + w₃ • c` is `w₂`. -/
theorem bary₂_combination {a b c : Point} (h : det a b c ≠ 0) {w₁ w₂ w₃ : ℝ}
    (hw : w₁ + w₂ + w₃ = 1) : bary₂ a b c (w₁ • a + w₂ • b + w₃ • c) = w₂ := by
  unfold bary₂
  rw [← det_cyclic_right, det_smul_add_smul_add_smul c a a b c w₁ w₂ w₃ hw]
  simp only [det_self_right, det_self_outer, mul_zero, zero_add, add_zero, det_cyclic_right]
  exact mul_div_cancel_right₀ _ h

@[simp] theorem bary₁_vertex_left {a b c : Point} (h : det a b c ≠ 0) : bary₁ a b c a = 1 := by
  unfold bary₁; exact div_self h
@[simp] theorem bary₂_vertex_left (a b c : Point) : bary₂ a b c a = 0 := by
  unfold bary₂; simp
@[simp] theorem bary₃_vertex_left (a b c : Point) : bary₃ a b c a = 0 := by
  unfold bary₃; simp
@[simp] theorem bary₁_vertex_mid (a b c : Point) : bary₁ a b c b = 0 := by
  unfold bary₁; simp
@[simp] theorem bary₂_vertex_mid {a b c : Point} (h : det a b c ≠ 0) : bary₂ a b c b = 1 := by
  unfold bary₂; exact div_self h
@[simp] theorem bary₃_vertex_mid (a b c : Point) : bary₃ a b c b = 0 := by
  unfold bary₃; simp
@[simp] theorem bary₁_vertex_right (a b c : Point) : bary₁ a b c c = 0 := by
  unfold bary₁; simp
@[simp] theorem bary₂_vertex_right (a b c : Point) : bary₂ a b c c = 0 := by
  unfold bary₂; simp
@[simp] theorem bary₃_vertex_right {a b c : Point} (h : det a b c ≠ 0) : bary₃ a b c c = 1 := by
  unfold bary₃; exact div_self h

/-- `bary₁` is continuous in the point. -/
theorem continuous_bary₁ (a b c : Point) : Continuous (bary₁ a b c) :=
  (continuous_det_left b c).div_const _

/-- `bary₂` is continuous in the point. -/
theorem continuous_bary₂ (a b c : Point) : Continuous (bary₂ a b c) :=
  (continuous_det_mid a c).div_const _

/-- `bary₃` is continuous in the point. -/
theorem continuous_bary₃ (a b c : Point) : Continuous (bary₃ a b c) :=
  (continuous_det_right a b).div_const _

/-- `bary₁` is affine along segments. -/
theorem bary₁_lerp (a b c p q : Point) (t : ℝ) :
    bary₁ a b c (lerp p q t) = (1 - t) * bary₁ a b c p + t * bary₁ a b c q := by
  unfold bary₁; rw [det_lerp_left]; ring

/-- `bary₂` is affine along segments. -/
theorem bary₂_lerp (a b c p q : Point) (t : ℝ) :
    bary₂ a b c (lerp p q t) = (1 - t) * bary₂ a b c p + t * bary₂ a b c q := by
  unfold bary₂; rw [det_lerp_mid]; ring

/-- `bary₃` is affine along segments. -/
theorem bary₃_lerp (a b c p q : Point) (t : ℝ) :
    bary₃ a b c (lerp p q t) = (1 - t) * bary₃ a b c p + t * bary₃ a b c q := by
  unfold bary₃; rw [det_lerp]; ring

/-- Membership in a nondegenerate triangle: all barycentric coordinates are nonnegative. -/
theorem mem_triangle_iff_bary {a b c : Point} (h : det a b c ≠ 0) {x : Point} :
    x ∈ convexHull ℝ ({a, b, c} : Set Point) ↔
      0 ≤ bary₁ a b c x ∧ 0 ≤ bary₂ a b c x ∧ 0 ≤ bary₃ a b c x := by
  rw [mem_convexHull_triple]
  constructor
  · rintro ⟨w₁, w₂, w₃, hw₁, hw₂, hw₃, hw, rfl⟩
    rw [bary₁_combination h hw, bary₂_combination h hw, bary₃_combination h hw]
    exact ⟨hw₁, hw₂, hw₃⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨_, _, _, h₁, h₂, h₃, bary_sum h x, bary_reconstruct h x⟩

/-! ### Topology of a triangle -/

/-- A triangle is convex. -/
theorem convex_triangle (a b c : Point) : Convex ℝ (convexHull ℝ ({a, b, c} : Set Point)) :=
  convex_convexHull ℝ _

/-- A triangle is compact. -/
theorem isCompact_triangle (a b c : Point) :
    IsCompact (convexHull ℝ ({a, b, c} : Set Point)) :=
  isCompact_convexHull_of_finite (((Set.finite_singleton c).insert b).insert a)

/-- A triangle is closed. -/
theorem isClosed_triangle (a b c : Point) : IsClosed (convexHull ℝ ({a, b, c} : Set Point)) :=
  (isCompact_triangle a b c).isClosed

/-- A triangle is bounded. -/
theorem triangle_bounded (a b c : Point) :
    IsBoundedSet (convexHull ℝ ({a, b, c} : Set Point)) :=
  isBoundedSet_of_isCompact (isCompact_triangle a b c)

/-- The open set `{0 < bary₁} ∩ {0 < bary₂} ∩ {0 < bary₃}`. -/
theorem isOpen_bary_pos (a b c : Point) :
    IsOpen {x : Point | 0 < bary₁ a b c x ∧ 0 < bary₂ a b c x ∧ 0 < bary₃ a b c x} := by
  have h₁ := isOpen_lt (continuous_const (y := (0 : ℝ))) (continuous_bary₁ a b c)
  have h₂ := isOpen_lt (continuous_const (y := (0 : ℝ))) (continuous_bary₂ a b c)
  have h₃ := isOpen_lt (continuous_const (y := (0 : ℝ))) (continuous_bary₃ a b c)
  exact h₁.inter (h₂.inter h₃)

/-- Auxiliary: if `f` is affine along `lerp v x`, nonnegative on `T`, `f v = 1` and
`f x = 0`, then `x` is not an interior point of `T`. -/
theorem not_mem_interior_of_affine_zero {T : Set Point} {v x : Point} {f : Point → ℝ}
    (hT : ∀ y ∈ T, 0 ≤ f y) (hf : ∀ s : ℝ, f (lerp v x s) = (1 - s) * f v + s * f x)
    (hv : f v = 1) (hx : f x = 0) : x ∉ interior T := by
  intro hint
  rw [mem_interior_iff_mem_nhds] at hint
  have hc : ContinuousAt (lerp v x) 1 := (continuous_lerp v x).continuousAt
  have hpre : ∀ᶠ s in 𝓝 (1 : ℝ), lerp v x s ∈ T := by
    have := hc.preimage_mem_nhds (by rwa [lerp_one])
    exact this
  have h1 : ∀ᶠ s in 𝓝[>] (1 : ℝ), lerp v x s ∈ T := hpre.filter_mono nhdsWithin_le_nhds
  obtain ⟨s, hs, hs1⟩ := (h1.and self_mem_nhdsWithin).exists
  have := hT _ hs
  rw [hf, hv, hx] at this
  have hs1' : (1 : ℝ) < s := hs1
  linarith

/-- The interior of a nondegenerate triangle: all barycentric coordinates positive. -/
theorem interior_triangle {a b c : Point} (h : det a b c ≠ 0) :
    interior (convexHull ℝ ({a, b, c} : Set Point)) =
      {x | 0 < bary₁ a b c x ∧ 0 < bary₂ a b c x ∧ 0 < bary₃ a b c x} := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxT := interior_subset hx
    rw [mem_triangle_iff_bary h] at hxT
    obtain ⟨h₁, h₂, h₃⟩ := hxT
    refine ⟨lt_of_le_of_ne h₁ ?_, lt_of_le_of_ne h₂ ?_, lt_of_le_of_ne h₃ ?_⟩
    · intro h0
      refine not_mem_interior_of_affine_zero (v := a) (f := bary₁ a b c) ?_
        (bary₁_lerp a b c a x) (bary₁_vertex_left h) h0.symm hx
      intro y hy; exact ((mem_triangle_iff_bary h).1 hy).1
    · intro h0
      refine not_mem_interior_of_affine_zero (v := b) (f := bary₂ a b c) ?_
        (bary₂_lerp a b c b x) (bary₂_vertex_mid h) h0.symm hx
      intro y hy; exact ((mem_triangle_iff_bary h).1 hy).2.1
    · intro h0
      refine not_mem_interior_of_affine_zero (v := c) (f := bary₃ a b c) ?_
        (bary₃_lerp a b c c x) (bary₃_vertex_right h) h0.symm hx
      intro y hy; exact ((mem_triangle_iff_bary h).1 hy).2.2
  · apply interior_maximal _ (isOpen_bary_pos a b c)
    rintro x ⟨h₁, h₂, h₃⟩
    exact (mem_triangle_iff_bary h).2 ⟨h₁.le, h₂.le, h₃.le⟩

/-- Membership in the interior of a nondegenerate triangle. -/
theorem mem_interior_triangle_iff {a b c : Point} (h : det a b c ≠ 0) {x : Point} :
    x ∈ interior (convexHull ℝ ({a, b, c} : Set Point)) ↔
      0 < bary₁ a b c x ∧ 0 < bary₂ a b c x ∧ 0 < bary₃ a b c x := by
  rw [interior_triangle h]; rfl

/-- The centroid of a triangle. -/
noncomputable def centroid (a b c : Point) : Point :=
  (1 / 3 : ℝ) • a + (1 / 3 : ℝ) • b + (1 / 3 : ℝ) • c

/-- The centroid is an interior point of a nondegenerate triangle. -/
theorem centroid_mem_interior {a b c : Point} (h : det a b c ≠ 0) :
    centroid a b c ∈ interior (convexHull ℝ ({a, b, c} : Set Point)) := by
  rw [mem_interior_triangle_iff h]
  have hw : (1 / 3 : ℝ) + 1 / 3 + 1 / 3 = 1 := by norm_num
  unfold centroid
  rw [bary₁_combination h hw, bary₂_combination h hw, bary₃_combination h hw]
  norm_num

/-- A nondegenerate triangle has nonempty interior. -/
theorem interior_triangle_nonempty {a b c : Point} (h : det a b c ≠ 0) :
    (interior (convexHull ℝ ({a, b, c} : Set Point))).Nonempty :=
  ⟨_, centroid_mem_interior h⟩

/-- The closure of the interior of a nondegenerate triangle is the triangle. -/
theorem closure_interior_triangle {a b c : Point} (h : det a b c ≠ 0) :
    closure (interior (convexHull ℝ ({a, b, c} : Set Point))) =
      convexHull ℝ ({a, b, c} : Set Point) := by
  rw [(convex_triangle a b c).closure_interior_eq_closure_of_nonempty_interior
    (interior_triangle_nonempty h)]
  exact (isClosed_triangle a b c).closure_eq

/-- Interior points of a triangle are not vertices. -/
theorem interior_triangle_subset_triangle (a b c : Point) :
    interior (convexHull ℝ ({a, b, c} : Set Point)) ⊆ convexHull ℝ ({a, b, c} : Set Point) :=
  interior_subset

/-! ### Faces -/

/-- The edge `a b` lies in the triangle. -/
theorem segment_subset_triangle_left (a b c : Point) :
    ArtGallery.segment a b ⊆ convexHull ℝ ({a, b, c} : Set Point) :=
  segment_subset_convexHull (by simp) (by simp)

/-- The edge `b c` lies in the triangle. -/
theorem segment_subset_triangle_mid (a b c : Point) :
    ArtGallery.segment b c ⊆ convexHull ℝ ({a, b, c} : Set Point) :=
  segment_subset_convexHull (by simp) (by simp)

/-- The edge `a c` lies in the triangle. -/
theorem segment_subset_triangle_right (a b c : Point) :
    ArtGallery.segment a c ⊆ convexHull ℝ ({a, b, c} : Set Point) :=
  segment_subset_convexHull (by simp) (by simp)

/-- On the edge `a b`, the third barycentric coordinate vanishes (no nondegeneracy needed). -/
theorem bary₃_eq_zero_of_mem_segment {a b c x : Point} (hx : x ∈ ArtGallery.segment a b) :
    bary₃ a b c x = 0 := by
  unfold bary₃; rw [det_eq_zero_of_mem_segment hx, zero_div]

/-- On the edge `b c`, the first barycentric coordinate vanishes. -/
theorem bary₁_eq_zero_of_mem_segment {a b c x : Point} (hx : x ∈ ArtGallery.segment b c) :
    bary₁ a b c x = 0 := by
  unfold bary₁; rw [← det_cyclic, det_eq_zero_of_mem_segment hx, zero_div]

/-- On the edge `a c`, the second barycentric coordinate vanishes. -/
theorem bary₂_eq_zero_of_mem_segment {a b c x : Point} (hx : x ∈ ArtGallery.segment a c) :
    bary₂ a b c x = 0 := by
  unfold bary₂; rw [det_swap23, det_eq_zero_of_mem_segment hx, neg_zero, zero_div]

/-- A point of a nondegenerate triangle with `bary₃ = 0` lies on the edge `a b`. -/
theorem mem_segment_of_bary₃_eq_zero {a b c : Point} (h : det a b c ≠ 0) {x : Point}
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set Point)) (h3 : bary₃ a b c x = 0) :
    x ∈ ArtGallery.segment a b := by
  obtain ⟨h₁, h₂, -⟩ := (mem_triangle_iff_bary h).1 hx
  have hs := bary_sum h x
  have hr := bary_reconstruct h x
  rw [h3, zero_smul, add_zero] at hr
  rw [h3, add_zero] at hs
  exact mem_segment_iff_weights.2 ⟨_, _, h₁, h₂, hs, hr.symm⟩

/-- A point of a nondegenerate triangle with `bary₁ = 0` lies on the edge `b c`. -/
theorem mem_segment_of_bary₁_eq_zero {a b c : Point} (h : det a b c ≠ 0) {x : Point}
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set Point)) (h1 : bary₁ a b c x = 0) :
    x ∈ ArtGallery.segment b c := by
  obtain ⟨-, h₂, h₃⟩ := (mem_triangle_iff_bary h).1 hx
  have hs := bary_sum h x
  have hr := bary_reconstruct h x
  rw [h1, zero_smul, zero_add] at hr
  rw [h1, zero_add] at hs
  exact mem_segment_iff_weights.2 ⟨_, _, h₂, h₃, hs, hr.symm⟩

/-- A point of a nondegenerate triangle with `bary₂ = 0` lies on the edge `a c`. -/
theorem mem_segment_of_bary₂_eq_zero {a b c : Point} (h : det a b c ≠ 0) {x : Point}
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set Point)) (h2 : bary₂ a b c x = 0) :
    x ∈ ArtGallery.segment a c := by
  obtain ⟨h₁, -, h₃⟩ := (mem_triangle_iff_bary h).1 hx
  have hs := bary_sum h x
  have hr := bary_reconstruct h x
  rw [h2, zero_smul, add_zero] at hr
  rw [h2, add_zero] at hs
  exact mem_segment_iff_weights.2 ⟨_, _, h₁, h₃, hs, hr.symm⟩

/-- The face `a b` of a nondegenerate triangle is exactly `{bary₃ = 0}` inside it. -/
theorem mem_segment_iff_bary₃_eq_zero {a b c : Point} (h : det a b c ≠ 0) {x : Point} :
    x ∈ ArtGallery.segment a b ↔
      x ∈ convexHull ℝ ({a, b, c} : Set Point) ∧ bary₃ a b c x = 0 :=
  ⟨fun hx => ⟨segment_subset_triangle_left a b c hx, bary₃_eq_zero_of_mem_segment hx⟩,
   fun ⟨hx, h3⟩ => mem_segment_of_bary₃_eq_zero h hx h3⟩

/-- The face `b c` of a nondegenerate triangle is exactly `{bary₁ = 0}` inside it. -/
theorem mem_segment_iff_bary₁_eq_zero {a b c : Point} (h : det a b c ≠ 0) {x : Point} :
    x ∈ ArtGallery.segment b c ↔
      x ∈ convexHull ℝ ({a, b, c} : Set Point) ∧ bary₁ a b c x = 0 :=
  ⟨fun hx => ⟨segment_subset_triangle_mid a b c hx, bary₁_eq_zero_of_mem_segment hx⟩,
   fun ⟨hx, h1⟩ => mem_segment_of_bary₁_eq_zero h hx h1⟩

/-- The face `a c` of a nondegenerate triangle is exactly `{bary₂ = 0}` inside it. -/
theorem mem_segment_iff_bary₂_eq_zero {a b c : Point} (h : det a b c ≠ 0) {x : Point} :
    x ∈ ArtGallery.segment a c ↔
      x ∈ convexHull ℝ ({a, b, c} : Set Point) ∧ bary₂ a b c x = 0 :=
  ⟨fun hx => ⟨segment_subset_triangle_right a b c hx, bary₂_eq_zero_of_mem_segment hx⟩,
   fun ⟨hx, h2⟩ => mem_segment_of_bary₂_eq_zero h hx h2⟩

/-- A point of a nondegenerate triangle that is not interior lies on one of the three edges. -/
theorem mem_edge_of_not_mem_interior {a b c : Point} (h : det a b c ≠ 0) {x : Point}
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set Point))
    (hint : x ∉ interior (convexHull ℝ ({a, b, c} : Set Point))) :
    x ∈ ArtGallery.segment a b ∨ x ∈ ArtGallery.segment b c ∨ x ∈ ArtGallery.segment a c := by
  obtain ⟨h₁, h₂, h₃⟩ := (mem_triangle_iff_bary h).1 hx
  rw [mem_interior_triangle_iff h] at hint
  by_cases e₁ : bary₁ a b c x = 0
  · exact Or.inr (Or.inl (mem_segment_of_bary₁_eq_zero h hx e₁))
  by_cases e₂ : bary₂ a b c x = 0
  · exact Or.inr (Or.inr (mem_segment_of_bary₂_eq_zero h hx e₂))
  by_cases e₃ : bary₃ a b c x = 0
  · exact Or.inl (mem_segment_of_bary₃_eq_zero h hx e₃)
  exact absurd ⟨lt_of_le_of_ne h₁ (Ne.symm e₁), lt_of_le_of_ne h₂ (Ne.symm e₂),
    lt_of_le_of_ne h₃ (Ne.symm e₃)⟩ hint

/-! ### The specification's triangles -/

/-- `P.triSet t` unfolded. -/
theorem triSet_eq (P : Polygon) (t : Polygon.Triangle) :
    P.triSet t = convexHull ℝ ({P.vtx t.1, P.vtx t.2.1, P.vtx t.2.2} : Set Point) := rfl

/-- `P.triVertices t` unfolded. -/
theorem triVertices_eq (P : Polygon) (t : Polygon.Triangle) :
    P.triVertices t = ({P.vtx t.1, P.vtx t.2.1, P.vtx t.2.2} : Set Point) := rfl

/-- A valid triangle has nonzero determinant. -/
theorem det_ne_zero_of_validTriangle {P : Polygon} {t : Polygon.Triangle}
    (h : P.validTriangle t) : det (P.vtx t.1) (P.vtx t.2.1) (P.vtx t.2.2) ≠ 0 :=
  h.2.2.2

/-- The vertex points of a valid triangle are pairwise distinct. -/
theorem vtx_ne_of_validTriangle {P : Polygon} {t : Polygon.Triangle}
    (h : P.validTriangle t) :
    P.vtx t.1 ≠ P.vtx t.2.1 ∧ P.vtx t.2.1 ≠ P.vtx t.2.2 ∧ P.vtx t.1 ≠ P.vtx t.2.2 :=
  ne_of_det_ne_zero (det_ne_zero_of_validTriangle h)

/-- The indices of a valid triangle are pairwise distinct. -/
theorem index_ne_of_validTriangle {P : Polygon} {t : Polygon.Triangle}
    (h : P.validTriangle t) : t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2 := by
  obtain ⟨h₁, h₂, h₃⟩ := vtx_ne_of_validTriangle h
  exact ⟨fun e => h₁ (by rw [e]), fun e => h₂ (by rw [e]), fun e => h₃ (by rw [e])⟩

/-- The indices of a valid triangle are in range. -/
theorem index_lt_of_validTriangle {P : Polygon} {t : Polygon.Triangle}
    (h : P.validTriangle t) : t.1 < P.n ∧ t.2.1 < P.n ∧ t.2.2 < P.n :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- The vertices of a triangle lie in it. -/
theorem triVertices_subset_triSet (P : Polygon) (t : Polygon.Triangle) :
    P.triVertices t ⊆ P.triSet t :=
  subset_convexHull ℝ _

/-- `P.triSet t` is compact. -/
theorem isCompact_triSet (P : Polygon) (t : Polygon.Triangle) : IsCompact (P.triSet t) :=
  isCompact_triangle _ _ _

/-- `P.triSet t` is closed. -/
theorem isClosed_triSet (P : Polygon) (t : Polygon.Triangle) : IsClosed (P.triSet t) :=
  isClosed_triangle _ _ _

/-- `P.triSet t` is bounded. -/
theorem triSet_bounded (P : Polygon) (t : Polygon.Triangle) : IsBoundedSet (P.triSet t) :=
  triangle_bounded _ _ _

/-- `P.triSet t` is convex. -/
theorem convex_triSet (P : Polygon) (t : Polygon.Triangle) : Convex ℝ (P.triSet t) :=
  convex_triangle _ _ _

/-- A valid triangle has nonempty interior. -/
theorem interior_triSet_nonempty {P : Polygon} {t : Polygon.Triangle}
    (h : P.validTriangle t) : (interior (P.triSet t)).Nonempty :=
  interior_triangle_nonempty (det_ne_zero_of_validTriangle h)

/-- The interior of a valid triangle, via barycentric coordinates. -/
theorem interior_triSet {P : Polygon} {t : Polygon.Triangle} (h : P.validTriangle t) :
    interior (P.triSet t) =
      {x | 0 < bary₁ (P.vtx t.1) (P.vtx t.2.1) (P.vtx t.2.2) x ∧
           0 < bary₂ (P.vtx t.1) (P.vtx t.2.1) (P.vtx t.2.2) x ∧
           0 < bary₃ (P.vtx t.1) (P.vtx t.2.1) (P.vtx t.2.2) x} :=
  interior_triangle (det_ne_zero_of_validTriangle h)

end

end Geometry

end ArtGallery
