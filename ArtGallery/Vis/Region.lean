module

public import ArtGallery.Existence.Main

/-!
# Visibility library: the region and the components of the complement of the boundary

Basic facts about the closed region `P.filled` of a polygon, proved from the polygonal Jordan
curve theorem of `ArtGallery.Jordan`:

* the component (in the complement of the boundary) of a point of the open region lies in the
  open region, the component of an exterior point lies in the exterior
  (`component_subset_interior`, `component_subset_compl`); hence a preconnected set avoiding the
  boundary is entirely interior or entirely exterior (`subset_interior_of_preconnected`,
  `subset_compl_of_preconnected`);
* **convex containment** (`closure_subset_filled_of_convex`): a convex set whose interior meets no
  edge and contains a point of the region lies, with its closure, in the region;
* **exact region** (`filled_eq_of_frontier_subset`): a closed subset of the region containing
  the boundary, whose frontier lies in the boundary and which has a point off the boundary, is
  the whole region;
* seeing is symmetric (`sees_comm`).
-/

namespace ArtGallery.Vis

@[expose] public section

open Set Filter Topology Metric
open ArtGallery.Jordan

/-! ### Components of the complement of the boundary -/

/-- The component of a point of the open region lies in the open region. -/
theorem component_subset_interior (P : Polygon) {c : Point} (hc : c ∈ P.filled \ P.boundary) :
    connectedComponentIn P.boundaryᶜ c ⊆ P.filled \ P.boundary := by
  intro z hz
  have hzb : z ∉ P.boundary := connectedComponentIn_subset _ _ hz
  refine ⟨(mem_filled_iff_bounded P hzb).2 ?_, hzb⟩
  rw [← connectedComponentIn_eq hz]
  exact (mem_filled_iff_bounded P hc.2).1 hc.1

/-- The component of a point outside the region lies outside the region. -/
theorem component_subset_compl (P : Polygon) {c : Point} (hc : c ∉ P.filled) :
    connectedComponentIn P.boundaryᶜ c ⊆ P.filledᶜ := by
  intro z hz hzf
  have hzb : z ∉ P.boundary := connectedComponentIn_subset _ _ hz
  have hcb : c ∉ P.boundary := fun h => hc (Or.inl h)
  apply hc
  refine (mem_filled_iff_bounded P hcb).2 ?_
  rw [connectedComponentIn_eq hz]
  exact (mem_filled_iff_bounded P hzb).1 hzf

/-- A preconnected set avoiding the boundary that contains a point of the region lies in the open
region. -/
theorem subset_interior_of_preconnected (P : Polygon) {S : Set Point} (hS : IsPreconnected S)
    (hSb : S ⊆ P.boundaryᶜ) {c : Point} (hcS : c ∈ S) (hc : c ∈ P.filled) :
    S ⊆ P.filled \ P.boundary :=
  (hS.subset_connectedComponentIn hcS hSb).trans (component_subset_interior P ⟨hc, hSb hcS⟩)

/-- A preconnected set avoiding the boundary that contains a point outside the region lies
outside the region. -/
theorem subset_compl_of_preconnected (P : Polygon) {S : Set Point} (hS : IsPreconnected S)
    (hSb : S ⊆ P.boundaryᶜ) {c : Point} (hcS : c ∈ S) (hc : c ∉ P.filled) :
    S ⊆ P.filledᶜ :=
  (hS.subset_connectedComponentIn hcS hSb).trans (component_subset_compl P hc)

/-! ### Convex containment and the exact region -/

/-- **Convex containment.** A convex set whose interior meets no edge and contains a point of the
region lies, with its closure, in the region. -/
theorem closure_subset_filled_of_convex (P : Polygon) {Q : Set Point} (hQ : Convex ℝ Q)
    (hedge : ∀ i < P.n, Disjoint (interior Q) (P.edge i)) {z : Point} (hz : z ∈ interior Q)
    (hzP : z ∈ P.filled) : closure Q ⊆ P.filled := by
  have hIb : interior Q ⊆ P.boundaryᶜ := by
    rintro x hx ⟨i, hi, hxi⟩
    exact Set.disjoint_left.1 (hedge i hi) hx hxi
  have hI : interior Q ⊆ P.filled :=
    (subset_interior_of_preconnected P hQ.interior.isPreconnected hIb hz hzP).trans sdiff_subset
  rw [← hQ.closure_interior_eq_closure_of_nonempty_interior ⟨z, hz⟩]
  exact closure_minimal hI (Jordan.isClosed_filled P)

/-- **Exact region.** A closed set `U ⊆ P.filled` containing the boundary, whose frontier lies in
the boundary and which contains a point off the boundary, is the whole region. -/
theorem filled_eq_of_frontier_subset {P : Polygon} (hP : P.Simple) {U : Set Point}
    (hUc : IsClosed U) (hbd : P.boundary ⊆ U) (hfr : frontier U ⊆ P.boundary)
    (hU : U ⊆ P.filled) (hne : (U \ P.boundary).Nonempty) : P.filled = U := by
  refine Subset.antisymm (fun p hp => ?_) hU
  by_cases hpb : p ∈ P.boundary
  · exact hbd hpb
  obtain ⟨c, hcU, hcb⟩ := hne
  -- points off the boundary are not on the frontier of `U`
  have hint : ∀ x ∈ U, x ∉ P.boundary → x ∈ interior U := by
    intro x hxU hxb
    by_contra hxi
    exact hxb (hfr (show x ∈ closure U \ interior U from ⟨subset_closure hxU, hxi⟩))
  have hcover : P.filled \ P.boundary ⊆ interior U ∪ Uᶜ := by
    rintro x ⟨-, hxb⟩
    by_cases hxU : x ∈ U
    · exact Or.inl (hint x hxU hxb)
    · exact Or.inr hxU
  have hsub := (filled_sdiff_boundary_connected hP).subset_left_of_subset_union isOpen_interior
    hUc.isOpen_compl (disjoint_compl_right.mono_left interior_subset) hcover
    ⟨c, ⟨hU hcU, hcb⟩, hint c hcU hcb⟩
  exact interior_subset (hsub ⟨hp, hpb⟩)

/-! ### Seeing -/

/-- Seeing is symmetric. -/
theorem sees_comm {P : Polygon} {p q : Point} : P.Sees p q ↔ P.Sees q p := by
  show ArtGallery.segment p q ⊆ P.filled ↔ ArtGallery.segment q p ⊆ P.filled
  rw [Geometry.segment_comm]

end

end ArtGallery.Vis
