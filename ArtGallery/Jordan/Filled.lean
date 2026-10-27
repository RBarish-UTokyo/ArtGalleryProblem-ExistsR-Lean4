module

public import ArtGallery.Jordan.Parity
public import ArtGallery.Geometry.Det
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# The filled region: the easy direction and basic topology

* far below every vertex the parity is `false` (`parity_eq_false_of_far_below`), because the
  number of edges straddling an abscissa is even (`sum_straddleInd`);
* a point of odd parity has a bounded component (`odd_component_bounded`), hence lies in the
  filled region (`odd_mem_filled`);
* far points are not in the filled region (`far_not_mem_filled`: a far point has an unbounded
  ray in its component), so the filled region is bounded (`filled_bounded`);
* the plane is locally connected, components of open sets are open, and the filled region is
  closed (`isClosed_filled`) and compact (`isCompact_filled`).

Provenance: adapted from `Chazelle/Jordan/Filled.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery`.
-/

namespace ArtGallery.Jordan

@[expose] public section

open Set Filter Topology
open ArtGallery.Geometry (isBoundedSet_iff isBoundedSet_of_subset lerp)

/-! ### The number of straddling edges is even -/

/-- Indicator (in `ZMod 2`) that `u` has abscissa `≤ z.1`. -/
noncomputable def leInd (z u : Point) : ZMod 2 := if u.1 ≤ z.1 then 1 else 0

/-- Indicator (in `ZMod 2`) that the edge `u v` straddles the abscissa of `z`. -/
noncomputable def straddleInd (z u v : Point) : ZMod 2 := if straddles z u v then 1 else 0

/-- An edge straddles iff exactly one endpoint has abscissa `≤ z.1`. -/
theorem straddleInd_eq (z u v : Point) : straddleInd z u v = leInd z u + leInd z v := by
  unfold straddleInd leInd
  by_cases hu : u.1 ≤ z.1 <;> by_cases hv : v.1 ≤ z.1
  · have hs : ¬ straddles z u v := by
      rintro (⟨-, h⟩ | ⟨-, h⟩) <;> linarith
    rw [ite_eq_right hs, ite_eq_left hu, ite_eq_left hv]; decide
  · have hs : straddles z u v := Or.inl ⟨hu, not_le.1 hv⟩
    rw [ite_eq_left hs, ite_eq_left hu, ite_eq_right hv]; decide
  · have hs : straddles z u v := Or.inr ⟨hv, not_le.1 hu⟩
    rw [ite_eq_left hs, ite_eq_right hu, ite_eq_left hv]; decide
  · have hs : ¬ straddles z u v := by
      rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact hu h
      · exact hv h
    rw [ite_eq_right hs, ite_eq_right hu, ite_eq_right hv]; decide

/-- The number of edges straddling the abscissa of `z` is even. -/
theorem sum_straddleInd (P : Polygon) (z : Point) :
    ∑ i ∈ Finset.range P.n, straddleInd z (P.vtx i) (P.vtx ((i + 1) % P.n)) = 0 := by
  simp only [straddleInd_eq]
  rw [Finset.sum_add_distrib, sum_range_succ_mod (fun i => leInd z (P.vtx i)) P.n]
  exact zmod_two_add_self _

/-- A point strictly below both endpoints is crossed by the edge iff the edge straddles it. -/
theorem crosses_iff_straddles_of_below {z u v : Point} (hu : z.2 < u.2) (hv : z.2 < v.2) :
    crosses z u v ↔ straddles z u v := by
  constructor
  · exact crosses_straddles
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left
      refine ⟨h1, h2, ?_⟩
      nlinarith [mul_pos (sub_pos.2 hu) (sub_pos.2 h2), mul_nonneg (sub_pos.2 hv).le (sub_nonneg.2 h1)]
    · right
      refine ⟨h1, h2, ?_⟩
      nlinarith [mul_pos (sub_pos.2 hv) (sub_pos.2 h2), mul_nonneg (sub_pos.2 hu).le (sub_nonneg.2 h1)]

/-- **Far below**: a point below every vertex has crossing sum `0`. -/
theorem crossSum_eq_zero_of_far_below (P : Polygon) {z : Point} (hz : z.2 < -coordBound P) :
    crossSum P z = 0 := by
  unfold crossSum
  rw [← sum_straddleInd P z]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < P.n := Finset.mem_range.1 hi
  have hi2 : (i + 1) % P.n < P.n := Nat.mod_lt _ (by omega)
  have hu : z.2 < (P.vtx i).2 := hz.trans_le (abs_le.1 (abs_snd_vtx_le_coordBound P hi')).1
  have hv : z.2 < (P.vtx ((i + 1) % P.n)).2 :=
    hz.trans_le (abs_le.1 (abs_snd_vtx_le_coordBound P hi2)).1
  unfold crossInd straddleInd
  exact if_congr (crosses_iff_straddles_of_below hu hv) rfl rfl

/-- **Far below**: a point below every vertex has parity `false`. -/
theorem parity_eq_false_of_far_below (P : Polygon) {z : Point} (hz : z.2 < -coordBound P) :
    parity P z = false :=
  parity_eq_false_iff.2 (crossSum_eq_zero_of_far_below P hz)

/-- **Far away, all four directions**: a point outside the square of half-side `coordBound P`
has parity `false`. -/
theorem parity_eq_false_of_far_any (P : Polygon) {z : Point}
    (hz : coordBound P < z.1 ∨ z.1 < -coordBound P ∨ coordBound P < z.2 ∨ z.2 < -coordBound P) :
    parity P z = false := by
  rcases hz with h | h | h | h
  · exact parity_eq_false_iff.2 (crossSum_eq_zero_of_far P (Or.inl h))
  · exact parity_eq_false_iff.2 (crossSum_eq_zero_of_far P (Or.inr (Or.inl h)))
  · exact parity_eq_false_iff.2 (crossSum_eq_zero_of_far P (Or.inr (Or.inr h)))
  · exact parity_eq_false_of_far_below P h

/-- A point of odd parity lies in the square of half-side `coordBound P`. -/
theorem abs_le_coordBound_of_parity_true (P : Polygon) {z : Point} (hz : parity P z = true) :
    |z.1| ≤ coordBound P ∧ |z.2| ≤ coordBound P := by
  by_contra h
  rw [not_and_or, not_le, not_le, lt_abs, lt_abs] at h
  have : coordBound P < z.1 ∨ z.1 < -coordBound P ∨ coordBound P < z.2 ∨ z.2 < -coordBound P := by
    rcases h with (h | h) | (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (by linarith)))
  rw [parity_eq_false_of_far_any P this] at hz
  exact Bool.false_ne_true hz

/-! ### Points of the boundary are bounded by `coordBound` -/

/-- Every point of the boundary lies in the square of half-side `coordBound P`. -/
theorem abs_le_coordBound_of_mem_boundary (P : Polygon) {p : Point} (hp : p ∈ P.boundary) :
    |p.1| ≤ coordBound P ∧ |p.2| ≤ coordBound P := by
  obtain ⟨i, hi, t, ht0, ht1, rfl⟩ := hp
  have hi2 : (i + 1) % P.n < P.n := Nat.mod_lt _ (by omega)
  have h1 := abs_le.1 (abs_fst_vtx_le_coordBound P hi)
  have h2 := abs_le.1 (abs_snd_vtx_le_coordBound P hi)
  have h3 := abs_le.1 (abs_fst_vtx_le_coordBound P hi2)
  have h4 := abs_le.1 (abs_snd_vtx_le_coordBound P hi2)
  constructor
  · rw [abs_le]; constructor <;> simp only <;> nlinarith
  · rw [abs_le]; constructor <;> simp only <;> nlinarith

/-! ### Local connectedness of the plane -/

/-- The plane is locally connected (balls are convex). -/
instance instLocallyConnectedSpacePoint : LocallyConnectedSpace Point :=
  locallyConnectedSpace_of_connected_bases (fun x r => Metric.ball x r) (fun _ r => 0 < r)
    (fun _ => Metric.nhds_basis_ball) (fun x r _ => (convex_ball x r).isPreconnected)

/-- Components of the complement of the boundary are open. -/
theorem isOpen_connectedComponentIn_boundary_compl (P : Polygon) (z : Point) :
    IsOpen (connectedComponentIn P.boundaryᶜ z) :=
  (isOpen_boundary_compl P).connectedComponentIn

/-- The parity is constant on the component of a point off the boundary. -/
theorem parity_eq_of_mem_connectedComponentIn (P : Polygon) {z w : Point}
    (hw : w ∈ connectedComponentIn P.boundaryᶜ z) : parity P w = parity P z := by
  have hz : z ∈ P.boundaryᶜ := connectedComponentIn_nonempty_iff.1 ⟨w, hw⟩
  exact parity_eq_of_isPreconnected P isPreconnected_connectedComponentIn
    (connectedComponentIn_subset _ _) hw (mem_connectedComponentIn hz)

/-! ### Odd points have bounded components -/

/-- **Easy direction**: the component of a point of odd parity is bounded. -/
theorem odd_component_bounded (P : Polygon) {z : Point} (hodd : parity P z = true) :
    IsBoundedSet (connectedComponentIn P.boundaryᶜ z) := by
  refine ⟨coordBound P, fun w hw => ?_⟩
  have := parity_eq_of_mem_connectedComponentIn P hw
  rw [hodd] at this
  exact abs_le_coordBound_of_parity_true P this

/-- A point of odd parity belongs to the filled region. -/
theorem odd_mem_filled (P : Polygon) {z : Point} (hodd : parity P z = true) : z ∈ P.filled :=
  Or.inr (odd_component_bounded P hodd)

/-- The boundary is part of the filled region. -/
theorem boundary_subset_filled (P : Polygon) : P.boundary ⊆ P.filled := fun _ h => Or.inl h

/-- Membership in the filled region for a point off the boundary. -/
theorem mem_filled_iff_bounded (P : Polygon) {z : Point} (hz : z ∉ P.boundary) :
    z ∈ P.filled ↔ IsBoundedSet (connectedComponentIn P.boundaryᶜ z) := by
  constructor
  · rintro (h | h)
    · exact absurd h hz
    · exact h
  · exact Or.inr

/-! ### Rays and far points -/

/-- A real number can be pushed beyond any bound along a nonzero direction. -/
theorem exists_abs_add_mul_gt {c : ℝ} (hc : c ≠ 0) (w R : ℝ) : ∃ s : ℝ, 0 ≤ s ∧ R < |w + s * c| := by
  have hc' : 0 < |c| := abs_pos.2 hc
  refine ⟨(|R| + |w| + 1) / |c|, by positivity, ?_⟩
  have h1 : |(|R| + |w| + 1) / |c| * c| = |R| + |w| + 1 := by
    rw [abs_mul, abs_div, abs_abs, div_mul_cancel₀ _ hc'.ne']
    exact abs_of_pos (by positivity)
  have h2 := abs_add_le (-w) (w + (|R| + |w| + 1) / |c| * c)
  rw [abs_neg, show -w + (w + (|R| + |w| + 1) / |c| * c) = (|R| + |w| + 1) / |c| * c by ring,
    h1] at h2
  linarith [le_abs_self R]

/-- The ray `{w + s • d | 0 ≤ s}`. -/
def ray (w d : Point) : Set Point := (fun s : ℝ => w + s • d) '' Ici 0

theorem mem_ray_self (w d : Point) : w ∈ ray w d := ⟨0, le_rfl, by simp⟩

/-- A ray is preconnected. -/
theorem isPreconnected_ray (w d : Point) : IsPreconnected (ray w d) :=
  isPreconnected_Ici.image _ (by fun_prop : Continuous fun s : ℝ => w + s • d).continuousOn

/-- A ray with nonzero direction is unbounded. -/
theorem not_isBoundedSet_ray (w : Point) {d : Point} (hd : d ≠ 0) : ¬ IsBoundedSet (ray w d) := by
  rintro ⟨R, hR⟩
  by_cases h1 : d.1 = 0
  · have h2 : d.2 ≠ 0 := by
      intro h2; apply hd; exact Prod.ext h1 h2
    obtain ⟨s, hs0, hs⟩ := exists_abs_add_mul_gt h2 w.2 R
    have := (hR (w + s • d) ⟨s, hs0, rfl⟩).2
    simp only [Geometry.add_snd, Geometry.smul_snd] at this
    linarith [show w.2 + s * d.2 = w.2 + s * d.2 from rfl]
  · obtain ⟨s, hs0, hs⟩ := exists_abs_add_mul_gt h1 w.1 R
    have := (hR (w + s • d) ⟨s, hs0, rfl⟩).1
    simp only [Geometry.add_fst, Geometry.smul_fst] at this
    linarith

/-- If a ray from `w` avoids the boundary, the component of `w` is unbounded. -/
theorem not_isBoundedSet_connectedComponentIn_of_ray (P : Polygon) {w d : Point} (hd : d ≠ 0)
    (hray : ray w d ⊆ P.boundaryᶜ) : ¬ IsBoundedSet (connectedComponentIn P.boundaryᶜ w) := by
  intro hb
  exact not_isBoundedSet_ray w hd (isBoundedSet_of_subset hb
    ((isPreconnected_ray w d).subset_connectedComponentIn (mem_ray_self w d) hray))

/-- **Far points have unbounded components**: a point outside the square of half-side
`coordBound P` has an unbounded component (it contains a ray to infinity). -/
theorem not_isBoundedSet_connectedComponentIn_of_far (P : Polygon) {w : Point}
    (hw : coordBound P < w.1 ∨ w.1 < -coordBound P ∨ coordBound P < w.2 ∨ w.2 < -coordBound P) :
    ¬ IsBoundedSet (connectedComponentIn P.boundaryᶜ w) := by
  rcases hw with h | h | h | h
  · refine not_isBoundedSet_connectedComponentIn_of_ray P (d := (1, 0)) (by simp) ?_
    rintro _ ⟨s, hs, rfl⟩ hp
    have := (abs_le.1 (abs_le_coordBound_of_mem_boundary P hp).1).2
    simp only [Geometry.add_fst, Geometry.smul_fst] at this
    linarith [mem_Ici.1 hs]
  · refine not_isBoundedSet_connectedComponentIn_of_ray P (d := (-1, 0)) (by simp) ?_
    rintro _ ⟨s, hs, rfl⟩ hp
    have := (abs_le.1 (abs_le_coordBound_of_mem_boundary P hp).1).1
    simp only [Geometry.add_fst, Geometry.smul_fst] at this
    linarith [mem_Ici.1 hs]
  · refine not_isBoundedSet_connectedComponentIn_of_ray P (d := (0, 1)) (by simp) ?_
    rintro _ ⟨s, hs, rfl⟩ hp
    have := (abs_le.1 (abs_le_coordBound_of_mem_boundary P hp).2).2
    simp only [Geometry.add_snd, Geometry.smul_snd] at this
    linarith [mem_Ici.1 hs]
  · refine not_isBoundedSet_connectedComponentIn_of_ray P (d := (0, -1)) (by simp) ?_
    rintro _ ⟨s, hs, rfl⟩ hp
    have := (abs_le.1 (abs_le_coordBound_of_mem_boundary P hp).2).1
    simp only [Geometry.add_snd, Geometry.smul_snd] at this
    linarith [mem_Ici.1 hs]

/-- Far points are off the boundary. -/
theorem not_mem_boundary_of_far (P : Polygon) {w : Point}
    (hw : coordBound P < w.1 ∨ w.1 < -coordBound P ∨ coordBound P < w.2 ∨ w.2 < -coordBound P) :
    w ∉ P.boundary := by
  intro h
  have h1 := abs_le.1 (abs_le_coordBound_of_mem_boundary P h).1
  have h2 := abs_le.1 (abs_le_coordBound_of_mem_boundary P h).2
  rcases hw with hw | hw | hw | hw <;> linarith

/-- Far points are not in the filled region. -/
theorem far_not_mem_filled (P : Polygon) {w : Point}
    (hw : coordBound P < w.1 ∨ w.1 < -coordBound P ∨ coordBound P < w.2 ∨ w.2 < -coordBound P) :
    w ∉ P.filled := by
  rintro (h | h)
  · exact not_mem_boundary_of_far P hw h
  · exact not_isBoundedSet_connectedComponentIn_of_far P hw h

/-- The filled region lies in the square of half-side `coordBound P`. -/
theorem filled_subset_square (P : Polygon) :
    P.filled ⊆ {p | |p.1| ≤ coordBound P ∧ |p.2| ≤ coordBound P} := by
  intro p hp
  by_contra h
  apply far_not_mem_filled P _ hp
  change ¬ (|p.1| ≤ coordBound P ∧ |p.2| ≤ coordBound P) at h
  rw [not_and_or, not_le, not_le, lt_abs, lt_abs] at h
  rcases h with (h | h) | (h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (by linarith)))

/-- **The filled region is bounded.** -/
theorem filled_bounded (P : Polygon) : IsBoundedSet P.filled :=
  ⟨coordBound P, fun _ hp => filled_subset_square P hp⟩

/-! ### The filled region is closed -/

/-- The complement of the filled region: points off the boundary with unbounded component. -/
theorem mem_filled_compl_iff (P : Polygon) {z : Point} :
    z ∈ P.filledᶜ ↔ z ∉ P.boundary ∧ ¬ IsBoundedSet (connectedComponentIn P.boundaryᶜ z) := by
  simp only [mem_compl_iff, Polygon.filled, mem_union, not_or]
  rfl

/-- The complement of the filled region is a union of components, hence open. -/
theorem isOpen_filled_compl (P : Polygon) : IsOpen P.filledᶜ := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  rw [mem_filled_compl_iff] at hz
  apply Filter.mem_of_superset
    ((isOpen_connectedComponentIn_boundary_compl P z).mem_nhds (mem_connectedComponentIn hz.1))
  intro w hw
  rw [mem_filled_compl_iff, ← connectedComponentIn_eq hw]
  exact ⟨connectedComponentIn_subset _ _ hw, hz.2⟩

/-- **The filled region is closed.** -/
theorem isClosed_filled (P : Polygon) : IsClosed P.filled :=
  isOpen_compl_iff.1 (isOpen_filled_compl P)

/-- **The filled region is compact.** -/
theorem isCompact_filled (P : Polygon) : IsCompact P.filled :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_filled P)
    (isBoundedSet_iff.1 (filled_bounded P))

end

end ArtGallery.Jordan
