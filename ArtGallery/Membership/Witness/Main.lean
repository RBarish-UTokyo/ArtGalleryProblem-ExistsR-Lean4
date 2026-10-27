module

public import ArtGallery.Membership.Witness.Visibility
public import ArtGallery.Membership.Witness.Cell

/-!
# The witness lemma (paper §3, pp. 13–15)

`guards_of_witnesses_core`: let `P` be simple, `Γ` a list of points of the region, and `L` a
list of lines containing the edge lines and the lines through a guard and a vertex.  If every
centroid of three intersection points of non-parallel lines of `L` that lies in the region is
seen by a guard, then the guards see the whole region.

Proof.  Suppose `p` is seen by no guard.  The set of points seen by no guard is open, and `p` is
a limit of interior points, so there is an interior point `p'` seen by no guard and lying on no
line of `L`.  Its cell `R` (points strictly on the side of `p'` of every line) is open, convex,
misses the boundary (edges lie on edge lines), hence lies in the component of `p'`, so it is a
bounded subset of the region.  Visibility from each guard is constant on `R`
(`sees_of_isPreconnected`), so no point of `R` is seen.  By the Krein–Milman theorem the closed
cell has three non-collinear extreme points, each an intersection of two non-parallel lines of
`L`, and their centroid lies in `R` — a contradiction.
-/

namespace ArtGallery.Membership.Witness

@[expose] public section

open Set Filter Topology Metric
open ArtGallery.Geometry (det_eq_zero_of_mem_segment isBoundedSet_iff isBoundedSet_of_subset)

/-- **Witness lemma (core form).**  `L` is any list of lines containing the edge lines and the
lines through a guard and a vertex, and `V` any set containing the intersection point of every
two non-parallel lines of `L`. -/
theorem guards_of_witnesses_core {P : Polygon} (hP : P.Simple) (Γ : List Point)
    (hΓ : ∀ γ ∈ Γ, γ ∈ P.filled) (L : List (Point × Point))
    (hLe : ∀ j < P.n, (P.vtx j, P.vtx ((j + 1) % P.n)) ∈ L)
    (hLg : ∀ γ ∈ Γ, ∀ k < P.n, (γ, P.vtx k) ∈ L) (V : Set Point)
    (hV : ∀ ℓ₁ ∈ L, ∀ ℓ₂ ∈ L, ∀ x : Point,
      (ℓ₁.2 - ℓ₁.1).1 * (ℓ₂.2 - ℓ₂.1).2 - (ℓ₁.2 - ℓ₁.1).2 * (ℓ₂.2 - ℓ₂.1).1 ≠ 0 →
        det ℓ₁.1 ℓ₁.2 x = 0 → det ℓ₂.1 ℓ₂.2 x = 0 → x ∈ V)
    (h : ∀ a ∈ V, ∀ b ∈ V, ∀ c ∈ V,
      ((a.1 + b.1 + c.1) / 3, (a.2 + b.2 + c.2) / 3) ∈ P.filled →
        ∃ γ ∈ Γ, P.Sees γ ((a.1 + b.1 + c.1) / 3, (a.2 + b.2 + c.2) / 3)) :
    ∀ p ∈ P.filled, ∃ γ ∈ Γ, P.Sees γ p := by
  intro p hp
  by_contra hno
  push Not at hno
  -- the set of points seen by no guard is open
  set U := {q : Point | ∀ γ ∈ Γ, ¬ P.Sees γ q} with hU
  have hUo : IsOpen U := by
    have e : U = ⋂ γ ∈ {x | x ∈ Γ}, {q | P.Sees γ q}ᶜ := by
      ext q
      simp only [hU, mem_ofPred_eq, mem_iInter, mem_compl_iff]
    rw [e]
    exact (List.finite_toSet Γ).isOpen_biInter fun γ _ => (isClosed_sees P γ).isOpen_compl
  -- an unseen interior point on no line of `L`
  have hcl : p ∈ closure (P.filled \ P.boundary) := by
    by_cases hpB : p ∈ P.boundary
    · exact Jordan.boundary_subset_closure_interior hP hpB
    · exact subset_closure ⟨hp, hpB⟩
  have hne : (U ∩ (P.filled \ P.boundary)).Nonempty :=
    mem_closure_iff.1 hcl U hUo hno
  obtain ⟨p', ⟨hp'U, hp'F, hp'B⟩, hgen⟩ :=
    exists_generic L (hUo.inter (Jordan.isOpen_filled_sdiff_boundary hP)) hne
  -- the cell of `p'`
  set R := cell L p' with hR
  have hRpc : IsPreconnected R := (convex_cell L p').isPreconnected
  have hp'R : p' ∈ R := mem_cell_self hgen
  have hedge : ∀ y ∈ R, ∀ j < P.n, det (P.vtx j) (P.vtx ((j + 1) % P.n)) y ≠ 0 :=
    fun y hy j hj => left_ne_zero_of_mul
      (hy _ (hLe j hj) (Jordan.simple_vtx_succ_ne hP hj)).ne'
  have hRB : R ⊆ P.boundaryᶜ := by
    rintro y hy ⟨j, hj, hyj⟩
    exact hedge y hy j hj (det_eq_zero_of_mem_segment hyj)
  have hRcomp : R ⊆ connectedComponentIn P.boundaryᶜ p' :=
    hRpc.subset_connectedComponentIn hp'R hRB
  have hbdd : IsBoundedSet (connectedComponentIn P.boundaryᶜ p') :=
    (Jordan.mem_filled_iff_bounded P hp'B).1 hp'F
  have hRF : R ⊆ P.filled := by
    intro y hy
    have hyB : y ∉ P.boundary := hRB hy
    rw [Jordan.mem_filled_iff_bounded P hyB, ← connectedComponentIn_eq (hRcomp hy)]
    exact hbdd
  -- no point of the cell is seen
  have hunseen : ∀ γ ∈ Γ, ∀ y ∈ R, ¬ P.Sees γ y := by
    intro γ hγ y hy hsy
    refine hp'U γ hγ (sees_of_isPreconnected hP (hΓ γ hγ) hRpc hedge ?_ hy hp'R hsy)
    intro y' hy' k hk hγk
    exact left_ne_zero_of_mul (hy' _ (hLg γ hγ k hk) hγk).ne'
  -- three non-collinear extreme points of the closed cell, and their centroid
  have hRb : Bornology.IsBounded R := isBoundedSet_iff.1 (isBoundedSet_of_subset hbdd hRcomp)
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := exists_noncollinear_extremePoints hgen hRb
  have hvert : ∀ e ∈ (ccell L p').extremePoints ℝ, e ∈ V := by
    intro e he
    obtain ⟨ℓ₁, h₁, ℓ₂, h₂, hD, e₁, e₂⟩ := exists_active_pair hgen he
    exact hV ℓ₁ h₁ ℓ₂ h₂ e hD e₁ e₂
  have hcen : cen a b c ∈ R := cen_mem_cell hgen ha.1 hb.1 hc.1 habc
  obtain ⟨γ, hγ, hsγ⟩ := h a (hvert a ha) b (hvert b hb) c (hvert c hc) (hRF hcen)
  exact hunseen γ hγ _ hcen hsγ

end

end ArtGallery.Membership.Witness
