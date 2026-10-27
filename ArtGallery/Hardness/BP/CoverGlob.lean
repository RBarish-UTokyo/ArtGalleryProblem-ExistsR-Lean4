module

public import ArtGallery.Hardness.BP.CoverSide

/-!
# Boundary-point variant, coverage: the pieces of the region of the global polygon

As `Sec5/CoverGlob.lean`.  The region of `polyCBP Φ n` is shown to be the union `globU Φ n` of the
main hexagon `hexSet` (unchanged), the `4n` pocket rooms with bays `pkU`, the regions of the
right units `rU` and the mirror images `lU` of the regions of the left units (`CoverRegion`).  This
file provides the pieces: `isClosed_globU`, `bdry_subset_globU` (the boundary lies in the union),
`globU_subset` (the union lies in the region).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace ArtGallery.BP.CoverM

open ArtGallery Set Polygon Filter Topology ArtGallery.Sec5
open ArtGallery.Sec5.CoverM (hexSet sS sTop sXL pwR pvR ptR ptL pvL pwL sS_big sS_lt_sTop
  isClosed_hexSet continuous_mirrorEquiv mem_mirror_image isClosed_mirror_image
  isClosed_affine_image mirrorEquiv_eq_mirrorR mem_hex_of seg_hex corners_hex)
open ArtGallery.Sec5.Count (mirrorEquiv mirrorEquiv_apply mirrorEquiv_mirrorEquiv)
open ArtGallery.BP.Count (filled_polyCBP_mirror)
open ArtGallery.Sec5.Corridor (CorridorAt c0 c1 d0 d1)
open ArtGallery.Sec5.Corridor.Input
open ArtGallery.Stade.Chain ArtGallery.Sec5.Glue

variable {Φ : List ETRINV.Constraint} {n : ℕ}

/-! ### The pieces -/

/-- The pocket room of slot `σ`. -/
noncomputable def pkU (Φ : List ETRINV.Constraint) (n : ℕ) (σ : ℕ) : Set Point :=
  (pocketPolyBP (slotOne n Φ σ) σ).filled

/-- The region of right unit `m`. -/
noncomputable def rU (Φ : List ETRINV.Constraint) (n : ℕ) (m : Fin (unitSpecs n Φ).1.length) :
    Set Point := CoverU.unitU n (numC Φ) m ((unitSpecs n Φ).1[m.1]'m.2)

/-- The region of left unit `m`, mirrored into the global frame. -/
noncomputable def lU (Φ : List ETRINV.Constraint) (n : ℕ) (m : Fin (unitSpecs n Φ).2.length) :
    Set Point := mirrorEquiv n '' CoverU.unitU n (numC Φ) m ((unitSpecs n Φ).2[m.1]'m.2)

/-- **The pieces of the region**: hexagon, pocket rooms, right units, mirrored left units. -/
noncomputable def globU (Φ : List ETRINV.Constraint) (n : ℕ) : Set Point :=
  hexSet Φ n ∪ (⋃ σ : Fin (4 * n), pkU Φ n σ) ∪ (⋃ m, rU Φ n m) ∪ (⋃ m, lU Φ n m)

theorem isClosed_unitU (k m : ℕ) (u : UnitSpec) : IsClosed (CoverU.unitU n k m u) := by
  refine ((Polygon.isClosed_filled _).union ?_).union ?_
  · exact isClosed_affine_image _ CoverT.isClosed_chanSet
  · exact isClosed_affine_image _ (Polygon.isClosed_filled _)

/-- **The union of the pieces is closed.** -/
theorem isClosed_globU : IsClosed (globU Φ n) := by
  refine ((isClosed_hexSet.union ?_).union ?_).union ?_
  · exact isClosed_iUnion_of_finite fun σ => Polygon.isClosed_filled _
  · exact isClosed_iUnion_of_finite fun m => isClosed_unitU _ _ _
  · exact isClosed_iUnion_of_finite fun m => isClosed_mirror_image (isClosed_unitU _ _ _)

/-! ### The pieces lie in the region -/

section Pieces

variable (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n)
include hΦ hn

theorem pkU_subset {σ : ℕ} (hσ : σ < 4 * n) : pkU Φ n σ ⊆ (polyCBP Φ n).filled := by
  intro q hq
  have hM := mainHypBP hΦ hn
  have hs := sees_pocketRoomBP hM.simple hM.ccw (hM.pocket σ hσ) (boxSepBP hΦ hn hσ (T := 1)
    (by have := sS_big (Φ := Φ) (n := n); linarith)) (g := ((slotX σ : ℝ) + 1 / 2, 0)) rfl
    (by simp only; linarith) (by simp only; linarith) (fun _ => rfl) hq
  exact hs (by rw [Geometry.segment_comm]; exact Geometry.left_mem_segment _ _)

theorem rU_subset (m : Fin (unitSpecs n Φ).1.length) : rU Φ n m ⊆ (polyCBP Φ n).filled := by
  have hQ := rightSideBP hΦ hn
  rintro z ((h | h) | h)
  · exact CoverU.corG_subset hQ m.2 h
  · exact CoverU.chanG_subset hQ m.2 h
  · exact CoverU.tkG_subset hQ m.2 h

theorem lU_subset (m : Fin (unitSpecs n Φ).2.length) : lU Φ n m ⊆ (polyCBP Φ n).filled := by
  have hQ := leftSideBP hΦ hn
  have hs : CoverU.unitU n (numC Φ) m ((unitSpecs n Φ).2[m.1]'m.2) ⊆ (polyMBP Φ n).filled := by
    rintro z ((h | h) | h)
    · exact CoverU.corG_subset hQ m.2 h
    · exact CoverU.chanG_subset hQ m.2 h
    · exact CoverU.tkG_subset hQ m.2 h
  rintro z ⟨w, hw, rfl⟩
  rw [filled_polyCBP_mirror]
  exact ⟨w, hs hw, rfl⟩

/-- **The pieces lie in the region.** -/
theorem globU_subset : globU Φ n ⊆ (polyCBP Φ n).filled := by
  rintro z (((h | h) | h) | h)
  · exact hex_subsetBP hΦ hn h
  · obtain ⟨σ, hσ⟩ := mem_iUnion.1 h
    exact pkU_subset hΦ hn σ.2 hσ
  · obtain ⟨m, hm⟩ := mem_iUnion.1 h
    exact rU_subset hΦ hn m hm
  · obtain ⟨m, hm⟩ := mem_iUnion.1 h
    exact lU_subset hΦ hn m hm

/-! ### The boundary lies in the union -/

theorem corners_hex : pwR n ∈ hexSet Φ n ∧ pvR Φ n ∈ hexSet Φ n ∧ ptR Φ n ∈ hexSet Φ n ∧
    ptL Φ n ∈ hexSet Φ n ∧ pvL Φ n ∈ hexSet Φ n ∧ (pwL : Point) ∈ hexSet Φ n := by
  have hS := sS_big (Φ := Φ) (n := n)
  have hT := sS_lt_sTop (Φ := Φ) (n := n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [hexSet, mem_ofPred_eq, det, pwR, pvR, ptR, ptL, pvL, pwL, sXL]
  refine ⟨⟨by nlinarith, by nlinarith, by norm_num, by linarith, by linarith, by linarith⟩,
    ⟨by nlinarith, by nlinarith, by linarith, by linarith, by linarith, le_rfl⟩,
    ⟨by nlinarith, by nlinarith, by linarith, le_rfl, by linarith, le_rfl⟩,
    ⟨by nlinarith, by nlinarith, by linarith, le_rfl, le_rfl, by linarith⟩,
    ⟨by nlinarith, by nlinarith, by linarith, by linarith, le_rfl, by linarith⟩,
    ⟨by nlinarith, by nlinarith, le_rfl, by linarith, by linarith, by linarith⟩⟩

/-- **The boundary lies in the union of the pieces.** -/
theorem bdry_subset_globU : (polyCBP Φ n).boundary ⊆ globU Φ n := by
  intro p hp
  have hS := sS_big (Φ := Φ) (n := n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := corners_hex (Φ := Φ) hΦ hn
  rcases polyCBP_bdry hΦ hn hp with ⟨σ, hσ, h⟩ | h | h | ⟨f, hf, h⟩ | h | h | ⟨f, hf, h⟩ | h
  · refine Or.inl (Or.inl (Or.inr (mem_iUnion.2 ⟨⟨σ, hσ⟩, ?_⟩)))
    have := chainSet_prefix_subset_boundary ((pocketBPClosed (slotOne n Φ σ) σ).map ratPoint) [] h
    rw [List.append_nil] at this
    exact Polygon.boundary_subset_filled _ this
  · exact Or.inl (Or.inl (Or.inl (seg_hex c1 c2 h)))
  · obtain ⟨e1, e2, e3⟩ := h
    refine Or.inl (Or.inl (Or.inl (mem_hex_of ?_ ?_ (by linarith) e3 ?_ e1.le)))
    · simp only [det, pwR, pvR]; rw [e1]; nlinarith
    · simp only [det, pvL, pwL, sXL]; rw [e1]; nlinarith
    · rw [e1]; simp only [sXL]; linarith
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
    have hj' : j < (unitSpecs n Φ).1.length := by simpa [sideChainsRBP, length_unitChainsBP] using hj
    refine Or.inl (Or.inr (mem_iUnion.2 ⟨⟨j, hj'⟩, ?_⟩))
    simp only [sideChainsRBP, List.getElem_map] at h
    rw [getElem_unitChainsBP, Nat.zero_add] at h
    exact CoverU.unitChain_subset (rightSideBP hΦ hn) hj' h
  · exact Or.inl (Or.inl (Or.inl (seg_hex c3 c4 h)))
  · obtain ⟨e1, e2, e3⟩ := h
    refine Or.inl (Or.inl (Or.inl (mem_hex_of ?_ ?_ (by linarith) e3 e1.ge ?_)))
    · simp only [det, pwR, pvR]; rw [e1]; simp only [sXL]; nlinarith
    · have hX : sXL Φ n ≤ -6 := by simp only [sXL]; linarith
      simp only [det, pvL, pwL]; rw [e1]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ -6 - sXL Φ n by linarith)
        (show (0 : ℝ) ≤ p.2 - sS Φ n by linarith)]
    · rw [e1]; simp only [sXL]; linarith
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
    have hj' : j < (unitSpecs n Φ).2.length := by simpa [sideChainsRBP, length_unitChainsBP] using hj
    refine Or.inr (mem_iUnion.2 ⟨⟨j, hj'⟩, ?_⟩)
    simp only [sideChainsRBP, List.getElem_map] at h
    rw [getElem_unitChainsBP, Nat.zero_add] at h
    rw [lU, mem_mirror_image, mirrorEquiv_eq_mirrorR]
    exact CoverU.unitChain_subset (leftSideBP hΦ hn) hj' h
  · exact Or.inl (Or.inl (Or.inl (seg_hex c5 c6 h)))

end Pieces

end ArtGallery.BP.CoverM

end
