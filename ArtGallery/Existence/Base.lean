module

public import ArtGallery.Existence.Combine
public import ArtGallery.Jordan.Jordan

/-!
# The base case: a simple polygon with three vertices is a triangle

For a simple polygon `P` with `P.n = 3`:

* `det_ne_zero_of_simple_three`: the three vertices are not collinear (if they were, the middle
  one would lie on the edge joining the other two, contradicting simplicity);
* `filled_eq_triangle`: the filled region is the closed triangle `convexHull ℝ {v₀, v₁, v₂}`
  (a point outside the triangle escapes along a ray on which one barycentric coordinate stays
  negative, so its component is unbounded; the component of a point inside is trapped in the
  open triangle, which is bounded);
* `weakTriangulates_triangle`, `triangulates_triangle`: `[(0, 1, 2)]` triangulates `P`.

Provenance: adapted from `Chazelle/Existence/Base.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery`.
-/

namespace ArtGallery.Existence

@[expose] public section

open Set Topology
open ArtGallery.Jordan

variable (P : Polygon)

/-! ### The edges and the boundary of a triangle -/

/-- Edge `0` of a polygon with three vertices. -/
theorem edge_zero_three (h3 : P.n = 3) : P.edge 0 = segment (P.vtx 0) (P.vtx 1) := by
  simp [Polygon.edge, h3]

/-- Edge `1` of a polygon with three vertices. -/
theorem edge_one_three (h3 : P.n = 3) : P.edge 1 = segment (P.vtx 1) (P.vtx 2) := by
  simp [Polygon.edge, h3]

/-- Edge `2` of a polygon with three vertices. -/
theorem edge_two_three (h3 : P.n = 3) : P.edge 2 = segment (P.vtx 2) (P.vtx 0) := by
  simp [Polygon.edge, h3]

/-- The boundary of a polygon with three vertices is the union of its three edges. -/
theorem mem_boundary_three (h3 : P.n = 3) {p : Point} :
    p ∈ P.boundary ↔ p ∈ segment (P.vtx 0) (P.vtx 1) ∨ p ∈ segment (P.vtx 1) (P.vtx 2) ∨
      p ∈ segment (P.vtx 2) (P.vtx 0) := by
  constructor
  · rintro ⟨i, hi, hp⟩
    rw [h3] at hi
    interval_cases i
    · exact Or.inl (by rw [← edge_zero_three P h3]; exact hp)
    · exact Or.inr (Or.inl (by rw [← edge_one_three P h3]; exact hp))
    · exact Or.inr (Or.inr (by rw [← edge_two_three P h3]; exact hp))
  · rintro (hp | hp | hp)
    · exact ⟨0, by omega, by rw [edge_zero_three P h3]; exact hp⟩
    · exact ⟨1, by omega, by rw [edge_one_three P h3]; exact hp⟩
    · exact ⟨2, by omega, by rw [edge_two_three P h3]; exact hp⟩

/-- The boundary of a polygon with three vertices lies in the triangle of its vertices. -/
theorem boundary_subset_triangle (h3 : P.n = 3) :
    P.boundary ⊆ convexHull ℝ ({P.vtx 0, P.vtx 1, P.vtx 2} : Set Point) := by
  intro p hp
  rcases (mem_boundary_three P h3).1 hp with h | h | h
  · exact Geometry.segment_subset_triangle_left _ _ _ h
  · exact Geometry.segment_subset_triangle_mid _ _ _ h
  · rw [segment_comm] at h; exact Geometry.segment_subset_triangle_right _ _ _ h

/-! ### Nondegeneracy -/

/-- **A simple polygon with three vertices is a nondegenerate triangle.** -/
theorem det_ne_zero_of_simple_three (hP : P.Simple) (h3 : P.n = 3) :
    det (P.vtx 0) (P.vtx 1) (P.vtx 2) ≠ 0 := by
  intro hdet
  have h01 : P.vtx 0 ≠ P.vtx 1 := simple_vtx_ne hP (by omega) (by omega) (by norm_num)
  have h02 : P.vtx 0 ≠ P.vtx 2 := simple_vtx_ne hP (by omega) (by omega) (by norm_num)
  have h12 : P.vtx 1 ≠ P.vtx 2 := simple_vtx_ne hP (by omega) (by omega) (by norm_num)
  obtain ⟨t, ht⟩ := Geometry.exists_lerp_of_det_eq_zero h01 hdet
  rcases lt_or_ge t 0 with ht0 | ht0
  · -- `v₀` lies strictly between `v₁` and `v₂`: on edge `1`
    have h1t : (1 : ℝ) - t ≠ 0 := by linarith
    have hv0 : P.vtx 0 = Geometry.lerp (P.vtx 1) (P.vtx 2) (1 / (1 - t)) := by
      rw [ht]
      apply Geometry.point_ext <;> simp only [Geometry.lerp_fst, Geometry.lerp_snd] <;>
        field_simp <;> ring
    have hmem : P.vtx 0 ∈ P.edge 1 := by
      rw [edge_one_three P h3, hv0]
      refine Geometry.lerp_mem_segment _ _ (div_nonneg zero_le_one (by linarith)) ?_
      rw [div_le_one (by linarith)]; linarith
    have := eq_endpoint_of_vtx_mem_edge hP (k := 0) (i := 1) (by omega) (by omega) hmem
    rw [h3] at this
    norm_num at this
    rcases this with h | h
    · exact h01 h
    · exact h02 h
  rcases le_or_gt t 1 with ht1 | ht1
  · -- `v₂` lies on edge `0`
    have hmem : P.vtx 2 ∈ P.edge 0 := by
      rw [edge_zero_three P h3, ht]
      exact Geometry.lerp_mem_segment _ _ ht0 ht1
    have := eq_endpoint_of_vtx_mem_edge hP (k := 2) (i := 0) (by omega) (by omega) hmem
    rw [h3] at this
    norm_num at this
    rcases this with h | h
    · exact h02 h.symm
    · exact h12 h.symm
  · -- `v₁` lies strictly between `v₀` and `v₂`: on edge `2`
    have ht0' : t ≠ 0 := by linarith
    have hv1 : P.vtx 1 = Geometry.lerp (P.vtx 0) (P.vtx 2) (1 / t) := by
      rw [ht]
      apply Geometry.point_ext <;> simp only [Geometry.lerp_fst, Geometry.lerp_snd] <;>
        field_simp <;> ring
    have hmem : P.vtx 1 ∈ P.edge 2 := by
      rw [edge_two_three P h3, segment_comm, hv1]
      refine Geometry.lerp_mem_segment _ _ (by positivity) ?_
      rw [div_le_one (by linarith)]; linarith
    have := eq_endpoint_of_vtx_mem_edge hP (k := 1) (i := 2) (by omega) (by omega) hmem
    rw [h3] at this
    norm_num at this
    rcases this with h | h
    · exact h12 h
    · exact h01 h.symm

/-! ### The boundary and the open triangle -/

/-- A point of the open triangle is not on the boundary. -/
theorem not_mem_boundary_of_mem_interior_triangle (h3 : P.n = 3)
    (hdet : det (P.vtx 0) (P.vtx 1) (P.vtx 2) ≠ 0) {z : Point}
    (hz : z ∈ interior (convexHull ℝ ({P.vtx 0, P.vtx 1, P.vtx 2} : Set Point))) :
    z ∉ P.boundary := by
  rw [Geometry.mem_interior_triangle_iff hdet] at hz
  intro hb
  rcases (mem_boundary_three P h3).1 hb with h | h | h
  · have := Geometry.bary₃_eq_zero_of_mem_segment (c := P.vtx 2) h
    linarith [hz.2.2]
  · have := Geometry.bary₁_eq_zero_of_mem_segment (a := P.vtx 0) h
    linarith [hz.1]
  · rw [segment_comm] at h
    have := Geometry.bary₂_eq_zero_of_mem_segment (b := P.vtx 1) h
    linarith [hz.2.1]

/-- A point of the closed triangle which is not in the open triangle is on the boundary. -/
theorem mem_boundary_of_not_mem_interior_triangle (h3 : P.n = 3)
    (hdet : det (P.vtx 0) (P.vtx 1) (P.vtx 2) ≠ 0) {z : Point}
    (hz : z ∈ convexHull ℝ ({P.vtx 0, P.vtx 1, P.vtx 2} : Set Point))
    (hint : z ∉ interior (convexHull ℝ ({P.vtx 0, P.vtx 1, P.vtx 2} : Set Point))) :
    z ∈ P.boundary := by
  rw [mem_boundary_three P h3]
  rcases Geometry.mem_edge_of_not_mem_interior hdet hz hint with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by rw [segment_comm]; exact h))

/-! ### Escaping along a ray -/

/-- **Escape lemma.**  Let `T ⊇ P.boundary` and `f` an affine function, nonnegative on `T`,
with `f v = 1` and `f z < 0`.  Then `z` is not in the filled region of `P`: the ray from `z`
away from `v` avoids `T`, hence the boundary, and is unbounded. -/
theorem not_mem_filled_of_neg_affine {P : Polygon} {T : Set Point} (hT : P.boundary ⊆ T)
    {f : Point → ℝ} (hTf : ∀ y ∈ T, 0 ≤ f y) {v z : Point}
    (hf : ∀ t : ℝ, f (Geometry.lerp v z t) = (1 - t) * f v + t * f z) (hv : f v = 1)
    (hz : f z < 0) : z ∉ P.filled := by
  have hzT : z ∉ T := fun h => absurd (hTf z h) (not_le.2 hz)
  have hzb : z ∉ P.boundary := fun h => hzT (hT h)
  have hvz : z - v ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h, hv] at hz
    linarith
  rw [mem_filled_iff_bounded P hzb]
  apply not_isBoundedSet_connectedComponentIn_of_ray P hvz
  rintro _ ⟨s, hs, rfl⟩
  have hs' : (0 : ℝ) ≤ s := hs
  have heq : z + s • (z - v) = Geometry.lerp v z (1 + s) := by
    rw [Geometry.lerp_eq_add_smul]
    apply Geometry.point_ext <;> simp <;> ring
  intro hb
  have hy := hTf _ (hT hb)
  simp only at hy
  rw [heq, hf, hv] at hy
  have : (1 + s) * f z < 0 := mul_neg_of_pos_of_neg (by linarith) hz
  linarith

/-! ### The filled region of a triangle -/

/-- **The filled region of a simple polygon with three vertices is the triangle of its
vertices.** -/
theorem filled_eq_triangle (hP : P.Simple) (h3 : P.n = 3) :
    P.filled = convexHull ℝ ({P.vtx 0, P.vtx 1, P.vtx 2} : Set Point) := by
  have hdet := det_ne_zero_of_simple_three P hP h3
  set T := convexHull ℝ ({P.vtx 0, P.vtx 1, P.vtx 2} : Set Point) with hTdef
  have hbT : P.boundary ⊆ T := boundary_subset_triangle P h3
  have hTf : ∀ y ∈ T, 0 ≤ Geometry.bary₁ (P.vtx 0) (P.vtx 1) (P.vtx 2) y ∧
      0 ≤ Geometry.bary₂ (P.vtx 0) (P.vtx 1) (P.vtx 2) y ∧
      0 ≤ Geometry.bary₃ (P.vtx 0) (P.vtx 1) (P.vtx 2) y :=
    fun y hy => (Geometry.mem_triangle_iff_bary hdet).1 hy
  ext z
  constructor
  · intro hz
    by_contra hzT
    rw [hTdef, Geometry.mem_triangle_iff_bary hdet] at hzT
    rcases not_and_or.1 hzT with h | h
    · exact not_mem_filled_of_neg_affine hbT (fun y hy => (hTf y hy).1)
        (Geometry.bary₁_lerp (P.vtx 0) (P.vtx 1) (P.vtx 2) (P.vtx 0) z)
        (Geometry.bary₁_vertex_left hdet) (not_le.1 h) hz
    rcases not_and_or.1 h with h | h
    · exact not_mem_filled_of_neg_affine hbT (fun y hy => (hTf y hy).2.1)
        (Geometry.bary₂_lerp (P.vtx 0) (P.vtx 1) (P.vtx 2) (P.vtx 1) z)
        (Geometry.bary₂_vertex_mid hdet) (not_le.1 h) hz
    · exact not_mem_filled_of_neg_affine hbT (fun y hy => (hTf y hy).2.2)
        (Geometry.bary₃_lerp (P.vtx 0) (P.vtx 1) (P.vtx 2) (P.vtx 2) z)
        (Geometry.bary₃_vertex_right hdet) (not_le.1 h) hz
  · intro hz
    by_cases hzb : z ∈ P.boundary
    · exact Or.inl hzb
    have hzint : z ∈ interior T := by
      by_contra h
      exact hzb (mem_boundary_of_not_mem_interior_triangle P h3 hdet hz h)
    refine Or.inr ?_
    have hcov : P.boundaryᶜ ⊆ interior T ∪ Tᶜ := by
      intro x hx
      by_cases hxT : x ∈ T
      · by_cases hxi : x ∈ interior T
        · exact Or.inl hxi
        · exact absurd (mem_boundary_of_not_mem_interior_triangle P h3 hdet hxT hxi) hx
      · exact Or.inr hxT
    have hdisj : Disjoint (interior T) Tᶜ :=
      Set.disjoint_left.2 fun x hx hx' => hx' (interior_subset hx)
    have hsub : connectedComponentIn P.boundaryᶜ z ⊆ interior T :=
      IsPreconnected.subset_left_of_subset_union isOpen_interior
        (Geometry.isClosed_triangle _ _ _).isOpen_compl hdisj
        ((connectedComponentIn_subset _ _).trans hcov)
        ⟨z, mem_connectedComponentIn hzb, hzint⟩ isPreconnected_connectedComponentIn
    exact Geometry.isBoundedSet_of_subset (Geometry.triangle_bounded _ _ _)
      (hsub.trans interior_subset)

/-! ### The triangulation of a triangle -/

/-- **A simple polygon with three vertices is weakly triangulated by its single triangle.** -/
theorem weakTriangulates_triangle (hP : P.Simple) (h3 : P.n = 3) :
    WeakTriangulates P [(0, 1, 2)] := by
  have hdet := det_ne_zero_of_simple_three P hP h3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [List.mem_singleton] at ht
    subst ht
    exact ⟨by rw [h3]; norm_num, by rw [h3]; norm_num, by rw [h3]; norm_num, hdet⟩
  · rw [h3]; rfl
  · rw [filled_eq_triangle P hP h3]
    ext p
    simp only [Set.mem_ofPred_eq, List.mem_singleton, exists_eq_left]
    rfl
  · exact List.pairwise_singleton _ _
  · intro t ht i hi _
    rw [List.mem_singleton] at ht
    subst ht
    rw [h3] at hi
    show P.vtx i ∈ ({P.vtx 0, P.vtx 1, P.vtx 2} : Set Point)
    interval_cases i <;> simp

/-- **A simple polygon with three vertices is triangulated by its single triangle.** -/
theorem triangulates_triangle (hP : P.Simple) (h3 : P.n = 3) : P.Triangulates [(0, 1, 2)] :=
  triangulates_of_weak (weakTriangulates_triangle P hP h3)

end

end ArtGallery.Existence
