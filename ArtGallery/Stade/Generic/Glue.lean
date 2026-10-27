module

public import ArtGallery.Stade.Exit

/-!
# Pieces glued along openings (proof plan L2.3, §12 item 5)

A finite family `S` of convex pieces (`Stade/Generic/Piece.lean`) is **glued along openings** when
every side of every piece either lies in the boundary of `P` or is glued to a side of another piece
of the family traversed in the opposite direction (`Glued K K' j j'`: side `j'` of `K'` is side `j`
of `K` reversed).  If moreover all vertices of all pieces lie on the boundary, every piece lies in
the region and the pieces cover the boundary, then the region is exactly the union of the pieces
(`filled_eq_pieceUnion`).  The proof applies `filled_eq_of_frontier_subset`: a point of the union
off the boundary is interior to a piece or lies in the relative interior of a glued side, where
the two pieces contain the two half-discs (`mem_interior_union_of_glued`).

Once the region is known to be covered by a finite family of closed sets, any sub-union is a room
whose door is the set of its points touching the other members (`isRoom_of_cover`,
`isRoom_pieceUnion`); this gives exit lemmas for unions of pieces.
-/

@[expose] public section

namespace ArtGallery.Stade

open Set Filter Topology Metric
open ArtGallery.Geometry (lerp det_lerp lerp_mem_segment)

variable {P : Polygon}

/-- Side `j` of `K` is glued to side `j'` of `K'`: side `j'` of `K'` is side `j` of `K` traversed
in the opposite direction. -/
def Glued (K K' : Polygon) (j j' : ℕ) : Prop :=
  j' < K'.n ∧ K'.vtx j' = K.vtx ((j + 1) % K.n) ∧ K'.vtx ((j' + 1) % K'.n) = K.vtx j

/-- The union of the pieces of a family. -/
def pieceUnion (S : Set Polygon) : Set Point := ⋃ K ∈ S, piece K

/-- Membership in the union of the pieces. -/
theorem mem_pieceUnion {S : Set Polygon} {x : Point} :
    x ∈ pieceUnion S ↔ ∃ K ∈ S, x ∈ piece K := by
  simp [pieceUnion]

/-- The union of finitely many pieces is closed. -/
theorem isClosed_pieceUnion {S : Set Polygon} (hS : S.Finite) : IsClosed (pieceUnion S) :=
  hS.isClosed_biUnion fun K _ => isClosed_piece K

/-- Each piece lies in the union. -/
theorem piece_subset_pieceUnion {S : Set Polygon} {K : Polygon} (hK : K ∈ S) :
    piece K ⊆ pieceUnion S := fun _ hx => mem_pieceUnion.2 ⟨K, hK, hx⟩

/-- **Two half-discs.** A point of the relative interior of a side `j` of `K` glued to a side of
`K'` is an interior point of `piece K ∪ piece K'`. -/
theorem mem_interior_union_of_glued {K K' : Polygon} (hK : IsPiece K) (hK' : IsPiece K')
    {j j' : ℕ} (hj : j < K.n) (hg : Glued K K' j j') {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    lerp (K.vtx j) (K.vtx ((j + 1) % K.n)) t ∈ interior (piece K ∪ piece K') := by
  obtain ⟨hj', e1, e2⟩ := hg
  obtain ⟨r₁, hr₁, h₁⟩ := near_open_side hK hj ht0 ht1
  obtain ⟨r₂, hr₂, h₂⟩ := near_open_side hK' hj' (t := 1 - t) (by linarith) (by linarith)
  rw [e1, e2, ← Geometry.lerp_symm] at h₂
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun z hz => ?_⟩
  rw [mem_ball] at hz
  rcases le_total 0 (det (K.vtx j) (K.vtx ((j + 1) % K.n)) z) with h | h
  · exact Or.inl (h₁ z (lt_of_lt_of_le hz (min_le_left _ _)) h)
  · refine Or.inr (h₂ z (lt_of_lt_of_le hz (min_le_right _ _)) ?_)
    rw [Geometry.det_swap12]; linarith

/-- **Exact region from glued pieces (L2.3).** Let `S` be a finite nonempty family of pieces of
the region of the simple polygon `P` such that
* every vertex of every piece lies on the boundary of `P`,
* every side of every piece lies in the boundary of `P` or is glued to a side of a piece of `S`,
* the pieces cover the boundary.
Then the region of `P` is the union of the pieces. -/
theorem filled_eq_pieceUnion (hP : P.Simple) {S : Set Polygon} (hS : S.Finite)
    (hpc : ∀ K ∈ S, IsPiece K) (hsub : ∀ K ∈ S, piece K ⊆ P.filled)
    (hvtx : ∀ K ∈ S, ∀ k < K.n, K.vtx k ∈ P.boundary)
    (hside : ∀ K ∈ S, ∀ j < K.n, K.edge j ⊆ P.boundary ∨ ∃ K' ∈ S, ∃ j', Glued K K' j j')
    (hbd : P.boundary ⊆ pieceUnion S) (hne : S.Nonempty) : P.filled = pieceUnion S := by
  have hU : pieceUnion S ⊆ P.filled := by
    intro x hx
    obtain ⟨K, hKS, hxK⟩ := mem_pieceUnion.1 hx
    exact hsub K hKS hxK
  have hne' : (pieceUnion S \ P.boundary).Nonempty := by
    obtain ⟨K, hKS⟩ := hne
    obtain ⟨o, ho⟩ := center_mem_interior (hpc K hKS)
    have h1 : o ∈ interior P.filled := interior_mono (hsub K hKS) ho
    rw [Jordan.interior_filled hP] at h1
    exact ⟨o, piece_subset_pieceUnion hKS (interior_subset ho), h1.2⟩
  refine Polygon.filled_eq_of_frontier_subset hP (isClosed_pieceUnion hS) hbd ?_ hU hne'
  intro y hy
  by_contra hyb
  have hyU : y ∈ pieceUnion S := (isClosed_pieceUnion hS).frontier_subset hy
  obtain ⟨K, hKS, hyK⟩ := mem_pieceUnion.1 hyU
  have hK := hpc K hKS
  have hnint : y ∉ interior (pieceUnion S) := hy.2
  by_cases hyi : y ∈ interior (piece K)
  · exact hnint (interior_mono (piece_subset_pieceUnion hKS) hyi)
  have hyfr : y ∈ frontier (piece K) := ⟨subset_closure hyK, hyi⟩
  obtain ⟨k, hk, hyk⟩ := mem_edge_of_mem_frontier hK hyfr
  rcases hside K hKS k hk with hb | ⟨K', hK'S, j', hg⟩
  · exact hyb (hb hyk)
  obtain ⟨t, ht0, ht1, hyt⟩ := hyk
  have hyt' : y = lerp (K.vtx k) (K.vtx ((k + 1) % K.n)) t := hyt
  rcases ht0.lt_or_eq with ht0' | ht0'
  · rcases ht1.lt_or_eq with ht1' | ht1'
    · have h := mem_interior_union_of_glued hK (hpc K' hK'S) hk hg ht0' ht1'
      rw [← hyt'] at h
      refine hnint (interior_mono ?_ h)
      exact union_subset (piece_subset_pieceUnion hKS) (piece_subset_pieceUnion hK'S)
    · rw [ht1', Geometry.lerp_one] at hyt'
      exact hyb (hyt' ▸ hvtx K hKS _ (succ_mod_lt hk))
  · rw [← ht0', Geometry.lerp_zero] at hyt'
    exact hyb (hyt' ▸ hvtx K hKS k hk)

/-- **Rooms from a cover.** If the region is covered by a finite family `𝒜` of closed sets, the
union of a subfamily `ℬ` is a room whose door is any set `D` containing every point of the union
that lies in a member of `𝒜 \ ℬ`. -/
theorem isRoom_of_cover {𝒜 ℬ : Set (Set Point)} (h𝒜 : 𝒜.Finite)
    (hcl : ∀ A ∈ 𝒜, IsClosed A) (hcov : P.filled ⊆ ⋃₀ 𝒜) (hℬ : ℬ ⊆ 𝒜) {D : Set Point}
    (hD : ∀ y ∈ ⋃₀ ℬ, y ∉ D → ∀ A ∈ 𝒜, A ∉ ℬ → y ∉ A) : P.IsRoom (⋃₀ ℬ) D := by
  refine ⟨(h𝒜.subset hℬ).isClosed_sUnion fun A hA => hcl A (hℬ hA), fun y hy _ hyD => ?_⟩
  have hC : IsClosed (⋃₀ (𝒜 \ ℬ)) :=
    (h𝒜.subset sdiff_subset).isClosed_sUnion fun A hA => hcl A hA.1
  have hyC : y ∉ ⋃₀ (𝒜 \ ℬ) := by
    rintro ⟨A, ⟨hA𝒜, hAℬ⟩, hyA⟩
    exact hD y hy hyD A hA𝒜 hAℬ hyA
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hC.isOpen_compl y hyC
  refine ⟨ε, hε, fun z hz hzy => ?_⟩
  obtain ⟨A, hA𝒜, hzA⟩ := hcov hz
  by_cases hAℬ : A ∈ ℬ
  · exact ⟨A, hAℬ, hzA⟩
  · exact absurd ⟨A, ⟨hA𝒜, hAℬ⟩, hzA⟩ (hball (mem_ball.2 hzy))

/-- **Rooms made of pieces.** If the region is covered by the pieces of a finite family `S`, the
union of the pieces of a subfamily `T` is a room whose door `D` contains every point of that union
lying in a piece of `S \ T`. -/
theorem isRoom_pieceUnion {S T : Set Polygon} (hS : S.Finite) (hcov : P.filled ⊆ pieceUnion S)
    (hTS : T ⊆ S) {D : Set Point}
    (hD : ∀ y ∈ pieceUnion T, y ∉ D → ∀ K ∈ S, K ∉ T → y ∉ piece K) :
    P.IsRoom (pieceUnion T) D := by
  refine ⟨isClosed_pieceUnion (hS.subset hTS), fun y hy _ hyD => ?_⟩
  have hC : IsClosed (pieceUnion (S \ T)) := isClosed_pieceUnion (hS.subset sdiff_subset)
  have hyC : y ∉ pieceUnion (S \ T) := by
    intro h
    obtain ⟨K, ⟨hKS, hKT⟩, hyK⟩ := mem_pieceUnion.1 h
    exact hD y hy hyD K hKS hKT hyK
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hC.isOpen_compl y hyC
  refine ⟨ε, hε, fun z hz hzy => ?_⟩
  obtain ⟨K, hKS, hzK⟩ := mem_pieceUnion.1 (hcov hz)
  by_cases hKT : K ∈ T
  · exact mem_pieceUnion.2 ⟨K, hKT, hzK⟩
  · have hmem : z ∈ pieceUnion (S \ T) := mem_pieceUnion.2 ⟨K, ⟨hKS, hKT⟩, hzK⟩
    exact absurd hmem (hball (mem_ball.2 hzy))

end ArtGallery.Stade

end
