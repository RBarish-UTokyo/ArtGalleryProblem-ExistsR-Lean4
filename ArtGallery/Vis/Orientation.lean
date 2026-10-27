module

public import ArtGallery.Vis.Local

/-!
# Visibility library: orientation

A simple polygon whose vertices all have ordinate `≥ y₀`, with an edge on the line `y = y₀`
traversed from left to right, has its interior to the left of every edge
(`leftInterior_of_bottom_edge`).

Proof: points below the line `y = y₀` are outside the region (a downward ray avoids the
boundary), so the right side of the bottom edge is exterior.  By the Jordan curve theorem
(`Jordan.two_components`) the right sides of all edges lie in one component of the complement of
the boundary and the left sides in another one, of different parity; hence all right sides are
exterior and all left sides interior.
-/

namespace ArtGallery.Vis

@[expose] public section

open Set Filter Topology Metric
open ArtGallery.Jordan

/-- **Orientation from a bottom edge.** A simple polygon whose vertices all have ordinate `≥ y₀`,
with an edge on the line `y = y₀` traversed from left to right, has its interior to the left of
every edge. -/
theorem leftInterior_of_bottom_edge {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n)
    {y₀ : ℝ} (hlow : ∀ j < P.n, y₀ ≤ (P.vtx j).2) (hu : (P.vtx i).2 = y₀)
    (hv : (P.vtx ((i + 1) % P.n)).2 = y₀) (hdir : (P.vtx i).1 < (P.vtx ((i + 1) % P.n)).1) :
    LeftInterior P := by
  obtain ⟨cL, cR, hcL, hcR, hne, -, hsides⟩ := two_components hP
  -- boundary points have ordinate `≥ y₀`
  have hbd : ∀ x ∈ P.boundary, y₀ ≤ x.2 := by
    rintro x ⟨j, hj, τ, hτ0, hτ1, rfl⟩
    have h1 := hlow j hj
    have h2 := hlow _ (succIdx_lt P hj)
    show y₀ ≤ (P.vtx j).2 + τ * ((P.vtx ((j + 1) % P.n)).2 - (P.vtx j).2)
    nlinarith [mul_nonneg hτ0 (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 hτ1) (sub_nonneg.2 h1)]
  -- points below the line `y = y₀` are outside the region
  have hbelow : ∀ x : Point, x.2 < y₀ → x ∉ P.filled := by
    intro x hx
    have hxb : x ∉ P.boundary := fun h => by linarith [hbd x h]
    rw [mem_filled_iff_bounded P hxb]
    refine not_isBoundedSet_connectedComponentIn_of_ray P (d := (0, -1)) (by simp) ?_
    rintro _ ⟨τ, hτ, rfl⟩ hp
    have := hbd _ hp
    simp only [Geometry.add_snd, Geometry.smul_snd] at this
    linarith [mem_Ici.1 hτ]
  -- the component of the right sides is exterior
  obtain ⟨δ, hδ, hδ0⟩ :=
    ((hsides i hi (1 / 2) ⟨by norm_num, by norm_num⟩).and self_mem_nhdsWithin).exists
  have hδ' : (0 : ℝ) < δ := hδ0
  have hRout : offset (P.vtx i) (P.vtx ((i + 1) % P.n)) (1 / 2) (-δ) ∉ P.filled := by
    apply hbelow
    rw [offset_snd, hu, hv]
    nlinarith [mul_pos hδ' (sub_pos.2 hdir)]
  have hcRout : cR ∉ P.filled := by
    have hsub := component_subset_compl P hRout
    rw [← connectedComponentIn_eq hδ.2] at hsub
    exact hsub (mem_connectedComponentIn hcR)
  -- the component of the left sides is interior
  have hcLin : cL ∈ P.filled \ P.boundary := by
    refine ⟨?_, hcL⟩
    rw [mem_filled_iff hP hcL]
    have hR : parity P cR = false := by
      rw [← Bool.not_eq_true, ← mem_filled_iff hP hcR]
      exact hcRout
    cases h : parity P cL
    · exact absurd (h.trans hR.symm) hne
    · rfl
  unfold LeftInterior
  intro j hj t ht0 ht1
  obtain ⟨δ₀, hδ₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hsides j hj t ⟨ht0, ht1⟩)
  refine ⟨δ₀, hδ₀, fun δ h0 h1 => ?_⟩
  obtain ⟨hl, hr⟩ := hsub ⟨h0, h1⟩
  have h1' := component_subset_interior P hcLin hl
  have h2' := component_subset_compl P hcRout hr
  rw [offset_eq] at h1'
  rw [offset_neg_eq] at h2'
  exact ⟨h1', h2'⟩

end

end ArtGallery.Vis
