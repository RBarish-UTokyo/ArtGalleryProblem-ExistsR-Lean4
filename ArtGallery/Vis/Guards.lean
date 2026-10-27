module

public import ArtGallery.Vis.Region

/-!
# Visibility library: guard sets

* the region of a simple polygon is infinite (`filled_infinite`), so guard sets can be padded
  (`HasGuardSetOfCard.mono`);
* a simple polygon with `n` vertices has a guard set of cardinality `n − 2`
  (`hasGuardSetOfCard_n_sub_two`): one corner of each triangle of a triangulation
  (`Existence.exists_triangulation`) sees the whole (convex) triangle;
* **the counting lemma** (`guards_in_region`, Lemmas 22/23 of Abrahamsen–Adamaszek–Miltzow).
-/

namespace ArtGallery.Vis

@[expose] public section

open Set
open ArtGallery.Jordan

/-! ### Padding -/

/-- The region of a simple polygon is infinite (it contains a nondegenerate edge). -/
theorem filled_infinite {P : Polygon} (hP : P.Simple) : P.filled.Infinite := by
  have h3 : 3 ≤ P.n := hP.1
  have h0 : 0 < P.n := by omega
  have huv := simple_vtx_succ_ne hP h0
  refine Set.infinite_of_injOn_mapsTo (Geometry.lerp_injective huv).injOn ?_
    (Set.Icc_infinite (zero_lt_one' ℝ))
  intro τ hτ
  exact Or.inl ⟨0, h0, Geometry.lerp_mem_segment _ _ hτ.1 hτ.2⟩

/-- A guard set can be enlarged by one point. -/
theorem hasGuardSetOfCard_succ {P : Polygon} (hP : P.Simple) {k : ℕ}
    (h : P.HasGuardSetOfCard k) : P.HasGuardSetOfCard (k + 1) := by
  classical
  obtain ⟨G, hG, hsub, hsee⟩ := h
  obtain ⟨x, hxf, hxG⟩ := (filled_infinite hP).exists_notMem_finset G
  refine ⟨insert x G, by rw [Finset.card_insert_of_notMem hxG, hG], ?_, ?_⟩
  · intro y hy
    rw [Finset.coe_insert] at hy
    rcases hy with rfl | hy
    · exact hxf
    · exact hsub hy
  · intro p hp
    obtain ⟨g, hg, hgp⟩ := hsee p hp
    refine ⟨g, ?_, hgp⟩
    rw [Finset.coe_insert]
    exact Or.inr hg

/-- **Padding.** A simple polygon with a guard set of cardinality `k` has one of every larger
cardinality (the region is infinite). -/
theorem HasGuardSetOfCard.mono {P : Polygon} (hP : P.Simple) {k k' : ℕ}
    (h : P.HasGuardSetOfCard k) (hk : k ≤ k') : P.HasGuardSetOfCard k' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => exact h
  | succ d ih => exact hasGuardSetOfCard_succ hP ih

/-! ### Guarding with `n − 2` guards -/

/-- **A simple polygon with `n` vertices has a guard set of cardinality `n − 2`** (one corner of
each triangle of a triangulation). -/
theorem hasGuardSetOfCard_n_sub_two {P : Polygon} (hP : P.Simple) :
    P.HasGuardSetOfCard (P.n - 2) := by
  classical
  obtain ⟨T, hT⟩ := Existence.exists_triangulation hP
  have hlen := Existence.triangulates_length hT
  obtain ⟨-, -, hunion, -, -⟩ := hT
  -- every triangle lies in the region
  have htri : ∀ t ∈ T, P.triSet t ⊆ P.filled := by
    intro t ht x hx
    rw [← hunion]
    exact ⟨t, ht, hx⟩
  have hcorner : ∀ t : Polygon.Triangle, P.vtx t.1 ∈ P.triSet t := fun t =>
    Geometry.triVertices_subset_triSet P t (Set.mem_insert _ _)
  refine HasGuardSetOfCard.mono hP ⟨(T.map fun t => P.vtx t.1).toFinset, rfl, ?_, ?_⟩ ?_
  · intro g hg
    rw [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hg
    obtain ⟨t, ht, rfl⟩ := hg
    exact htri t ht (hcorner t)
  · intro p hp
    rw [← hunion] at hp
    obtain ⟨t, ht, hpt⟩ := hp
    refine ⟨P.vtx t.1, ?_, ?_⟩
    · rw [Finset.mem_coe, List.mem_toFinset, List.mem_map]
      exact ⟨t, ht, rfl⟩
    · exact (Geometry.segment_subset_of_convex (Geometry.convex_triSet P t) (hcorner t) hpt).trans
        (htri t ht)
  · calc (T.map fun t => P.vtx t.1).toFinset.card ≤ (T.map fun t => P.vtx t.1).length :=
          List.toFinset_card_le _
      _ = T.length := List.length_map _
      _ = P.n - 2 := hlen

/-! ### The counting lemma -/

/-- **Lemma 22/23 of the paper (counting).** Let `A` be a part of the region and `M` a finite set
of points of `A` that are seen only from `A`, no two of them from a common point. Let `W` be a
nonempty set of points seen only from `A`, such that no point sees a point of `M` and a point of
`W`, and every point seeing all of `W` lies in `Spot`. Then every guard set has at least
`|M| + 1` guards in `A`, and if it has exactly `|M| + 1` guards in `A`, one of them lies in
`Spot`. -/
theorem guards_in_region {P : Polygon} (G : Finset Point) (hG : P.IsGuardSet (G : Set Point))
    (A : Set Point) [DecidablePred (· ∈ A)] (M : Finset Point) (W : Set Point) (Spot : Set Point)
    (hMA : ∀ m ∈ M, m ∈ P.filled) (hMonly : ∀ m ∈ M, ∀ p ∈ P.filled, P.Sees p m → p ∈ A)
    (hMdisj : ∀ m ∈ M, ∀ m' ∈ M, m ≠ m' → ∀ p, P.Sees p m → ¬ P.Sees p m')
    (hWne : W.Nonempty) (hWP : W ⊆ P.filled)
    (hWonly : ∀ w ∈ W, ∀ p ∈ P.filled, P.Sees p w → p ∈ A)
    (hMW : ∀ m ∈ M, ∀ w ∈ W, ∀ p, P.Sees p m → ¬ P.Sees p w)
    (hSpot : ∀ p ∈ P.filled, (∀ w ∈ W, P.Sees p w) → p ∈ Spot) :
    M.card + 1 ≤ (G.filter (· ∈ A)).card ∧
      ((G.filter (· ∈ A)).card = M.card + 1 → ∃ g ∈ G, g ∈ A ∧ g ∈ Spot) := by
  set GA := G.filter (· ∈ A)
  classical
  obtain ⟨hGf, hGsee⟩ := hG
  have hmemGA : ∀ g, g ∈ GA ↔ g ∈ G ∧ g ∈ A := fun _ => Finset.mem_filter
  -- a guard for every point of `M`
  have hm : ∀ m ∈ M, ∃ g ∈ G, P.Sees g m := fun m hm => by
    obtain ⟨g, hg, hgm⟩ := hGsee m (hMA m hm)
    exact ⟨g, hg, hgm⟩
  choose! f hfG hfsee using hm
  have hfA : ∀ m ∈ M, f m ∈ GA := fun m hm =>
    (hmemGA _).2 ⟨hfG m hm, hMonly m hm (f m) (hGf (hfG m hm)) (hfsee m hm)⟩
  have hfinj : Set.InjOn f M := by
    intro m hm m' hm' hmm'
    by_contra hne
    exact hMdisj m hm m' hm' hne (f m) (hfsee m hm) (hmm' ▸ hfsee m' hm')
  -- a guard for a point of `W`
  have hw : ∀ w ∈ W, ∃ g ∈ GA, P.Sees g w ∧ g ∉ M.image f := by
    intro w hw
    obtain ⟨g, hg, hgw⟩ := hGsee w (hWP hw)
    refine ⟨g, (hmemGA g).2 ⟨hg, hWonly w hw g (hGf hg) hgw⟩, hgw, ?_⟩
    intro hgM
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hgM
    exact hMW m hm w hw (f m) (hfsee m hm) hgw
  obtain ⟨w₀, hw₀⟩ := hWne
  obtain ⟨g₀, hg₀GA, hg₀w, hg₀M⟩ := hw w₀ hw₀
  have hsub : insert g₀ (M.image f) ⊆ GA := by
    intro g hg
    rw [Finset.mem_insert] at hg
    rcases hg with rfl | hg
    · exact hg₀GA
    · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hg
      exact hfA m hm
  have hcard : (insert g₀ (M.image f)).card = M.card + 1 := by
    rw [Finset.card_insert_of_notMem hg₀M, Finset.card_image_of_injOn hfinj]
  refine ⟨hcard.ge.trans (Finset.card_le_card hsub), fun heq => ?_⟩
  have hGAeq : insert g₀ (M.image f) = GA :=
    Finset.eq_of_subset_of_card_le hsub (heq.le.trans hcard.ge)
  have hg₀ := (hmemGA g₀).1 hg₀GA
  refine ⟨g₀, hg₀.1, hg₀.2, hSpot g₀ (hGf hg₀.1) fun w hwW => ?_⟩
  obtain ⟨g, hgGA, hgw, hgM⟩ := hw w hwW
  rw [← hGAeq, Finset.mem_insert] at hgGA
  rcases hgGA with rfl | hg
  · exact hgw
  · exact absurd hg hgM

end

end ArtGallery.Vis
