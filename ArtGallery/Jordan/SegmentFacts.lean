module

public import ArtGallery.Geometry.SpecExtra
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Elementary facts about `ArtGallery.segment`

Minimal segment facts needed by the crossing-parity theory (`ArtGallery.Jordan.Parity`):

* endpoints belong to the segment (`left_mem_segment`, `right_mem_segment`);
* symmetry (`segment_comm`);
* the parametrisation-free description of a non-vertical segment
  (`mem_segment_iff_of_lt`): for `u.1 < v.1`, a point `p` lies on `segment u v` iff
  `u.1 ≤ p.1 ≤ v.1` and `(p.2 - u.2) * (v.1 - u.1) = (v.2 - u.2) * (p.1 - u.1)`;
* membership in a vertical segment from the ordinate lying between the endpoints
  (`mem_segment_of_vertical`);
* a segment is closed (`isClosed_segment`), and the boundary of a polygon is closed
  (`isClosed_boundary`), its complement open (`isOpen_boundary_compl`).

Provenance: adapted from `Chazelle/Jordan/SegmentFacts.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery`; it imports `ArtGallery.Geometry.SpecExtra` instead of the specification.
-/

namespace ArtGallery.Jordan

public section

open Set

/-- Membership in a segment, unfolded. -/
theorem mem_segment_iff {u v p : Point} :
    p ∈ segment u v ↔
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = (u.1 + t * (v.1 - u.1), u.2 + t * (v.2 - u.2)) :=
  Iff.rfl

/-- The first endpoint lies on the segment. -/
theorem left_mem_segment (u v : Point) : u ∈ segment u v :=
  ⟨0, le_rfl, zero_le_one, by simp⟩

/-- The second endpoint lies on the segment. -/
theorem right_mem_segment (u v : Point) : v ∈ segment u v :=
  ⟨1, zero_le_one, le_rfl, by simp⟩

theorem segment_subset_comm {u v : Point} : segment u v ⊆ segment v u := by
  rintro p ⟨t, ht0, ht1, rfl⟩
  refine ⟨1 - t, by linarith, by linarith, ?_⟩
  ext <;> simp <;> ring

/-- A segment does not depend on the order of its endpoints. -/
theorem segment_comm (u v : Point) : segment u v = segment v u :=
  Subset.antisymm segment_subset_comm segment_subset_comm

/-- A point of a segment with `u.1 < v.1` has abscissa between the endpoints and lies on the
line through them (division-free form). -/
theorem mem_segment_iff_of_lt {u v p : Point} (huv : u.1 < v.1) :
    p ∈ segment u v ↔
      u.1 ≤ p.1 ∧ p.1 ≤ v.1 ∧ (p.2 - u.2) * (v.1 - u.1) = (v.2 - u.2) * (p.1 - u.1) := by
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    have hd : 0 < v.1 - u.1 := sub_pos.2 huv
    refine ⟨?_, ?_, ?_⟩
    · simp only
      nlinarith
    · simp only
      nlinarith
    · simp only
      ring
  · rintro ⟨h0, h1, hl⟩
    have hd : 0 < v.1 - u.1 := sub_pos.2 huv
    refine ⟨(p.1 - u.1) / (v.1 - u.1), div_nonneg (by linarith) hd.le,
      (div_le_one hd).2 (by linarith), ?_⟩
    ext
    · simp only
      field_simp
      ring
    · simp only
      field_simp
      linarith

/-- Membership in a vertical segment: same abscissa and ordinate between the endpoints. -/
theorem mem_segment_of_vertical {u v p : Point} (huv : u.1 = v.1) (hp : p.1 = u.1)
    (h0 : u.2 ≤ p.2) (h1 : p.2 ≤ v.2) : p ∈ segment u v := by
  by_cases hd : u.2 = v.2
  · refine ⟨0, le_rfl, zero_le_one, ?_⟩
    ext
    · simp [hp]
    · simp; linarith
  · have hd' : 0 < v.2 - u.2 := sub_pos.2 (lt_of_le_of_ne (h0.trans h1) hd)
    refine ⟨(p.2 - u.2) / (v.2 - u.2), div_nonneg (by linarith) hd'.le,
      (div_le_one hd').2 (by linarith), ?_⟩
    ext
    · simp [hp, huv]
    · simp only
      field_simp
      ring

/-- A point of a vertical segment has the common abscissa of the endpoints. -/
theorem fst_eq_of_mem_segment_vertical {u v p : Point} (huv : u.1 = v.1) (hp : p ∈ segment u v) :
    p.1 = u.1 := by
  obtain ⟨t, -, -, rfl⟩ := hp
  simp [huv]

/-- A segment is the continuous image of `[0,1]`, hence compact. -/
theorem isCompact_segment (u v : Point) : IsCompact (segment u v) := by
  have : segment u v =
      (fun t : ℝ => ((u.1 + t * (v.1 - u.1), u.2 + t * (v.2 - u.2)) : Point)) '' Icc 0 1 := by
    ext p
    simp only [mem_segment_iff, mem_image, mem_Icc]
    constructor
    · rintro ⟨t, h0, h1, rfl⟩; exact ⟨t, ⟨h0, h1⟩, rfl⟩
    · rintro ⟨t, ⟨h0, h1⟩, rfl⟩; exact ⟨t, h0, h1, rfl⟩
  rw [this]
  exact isCompact_Icc.image (by fun_prop)

/-- A segment is a closed set. -/
theorem isClosed_segment (u v : Point) : IsClosed (segment u v) :=
  (isCompact_segment u v).isClosed

/-- The boundary of a polygon as a finite union of edges. -/
theorem boundary_eq_biUnion (P : Polygon) :
    P.boundary = ⋃ i ∈ Finset.range P.n, P.edge i := by
  ext p
  simp [Polygon.boundary]

/-- Every edge of a polygon is closed. -/
theorem isClosed_edge (P : Polygon) (i : ℕ) : IsClosed (P.edge i) :=
  isClosed_segment _ _

/-- The boundary of a polygon is a closed set (a finite union of closed segments). -/
theorem isClosed_boundary (P : Polygon) : IsClosed P.boundary := by
  rw [boundary_eq_biUnion]
  exact isClosed_biUnion_finset fun i _ => isClosed_edge P i

/-- The complement of the boundary of a polygon is open. -/
theorem isOpen_boundary_compl (P : Polygon) : IsOpen P.boundaryᶜ :=
  (isClosed_boundary P).isOpen_compl

end

end ArtGallery.Jordan
