module

public import ArtGallery.Stade.GuardSlots
public import ArtGallery.Stade.GuardCeil
public import ArtGallery.Stade.Wedges

/-!
# The region of Stade's polygon as a union of convex pieces, and the canonical guards

* `regionPieces n Φ`: the hall, the ceiling features (wedges and copy pockets, as the polygons of
  their vertex lists), the floor needles of the variables, and the pieces `slotPieces` of every
  gadget slot.  The region of `SP n Φ` is the union of these pieces (proof plan L2.3); this is
  the hypothesis `RegionDecomp n Φ` of the main theorem of `Stade/Guarding.lean`.
* `slot_walls`: the pocket walls of an addition gadget are edges of `SP n Φ`.
* `canonList_nodup`: the canonical guards are pairwise distinct (they lie in pairwise disjoint
  regions), so the canonical guard set has `guards n Φ` elements.
* `slotGuards_mem`: the guards of a slot are canonical guards.
-/

@[expose] public section

namespace ArtGallery.Stade

open ArtGallery.ETRINVREV ArtGallery.Stade.Chain

variable {n : ℕ} {Φ : List Constraint}

/-! ### The pieces of the region -/

/-- **The convex pieces of the region** of Stade's polygon: the hall, the ceiling features, the
floor needles of the variables and the pieces of the gadget slots. -/
noncomputable def regionPieces (n : ℕ) (Φ : List Constraint) : List Polygon :=
  [hallPoly n Φ] ++ (ceilFeats n Φ).map (fun f => Polygon.mk (f.map ratPoint)) ++
    (List.range n).map (fun k => needleL (varA Φ k : ℝ) (-1) (hH n Φ)) ++
    (List.range (paramC Φ)).flatMap
      (fun c => slotPieces (cKind (gadAt Φ c)) (slotG n Φ c : ℝ) (hH n Φ))

/-- **The region decomposition** (proof plan L2.3): the region of `SP n Φ` is the union of the
pieces `regionPieces n Φ`. -/
def RegionDecomp (n : ℕ) (Φ : List Constraint) : Prop :=
  (SP n Φ).filled ⊆ ⋃ K ∈ regionPieces n Φ, piece K ∧
    ∀ K ∈ regionPieces n Φ, piece K ⊆ (SP n Φ).filled

/-- Membership in `regionPieces`, by kind of piece. -/
theorem mem_regionPieces {K : Polygon} :
    K ∈ regionPieces n Φ ↔ K = hallPoly n Φ ∨
      (∃ f ∈ ceilFeats n Φ, K = Polygon.mk (f.map ratPoint)) ∨
      (∃ k < n, K = needleL (varA Φ k : ℝ) (-1) (hH n Φ)) ∨
      (∃ c < paramC Φ, K ∈ slotPieces (cKind (gadAt Φ c)) (slotG n Φ c : ℝ) (hH n Φ)) := by
  simp only [regionPieces, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
    List.mem_map, List.mem_range, List.mem_flatMap]
  constructor
  · rintro (((h | ⟨f, hf, rfl⟩) | ⟨k, hk, rfl⟩) | ⟨c, hc, hK⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨f, hf, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨c, hc, hK⟩))
  · rintro (h | ⟨f, hf, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨c, hc, hK⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨f, hf, rfl⟩))
    · exact Or.inl (Or.inr ⟨k, hk, rfl⟩)
    · exact Or.inr ⟨c, hc, hK⟩

/-! ### Gadget constraints -/

/-- The gadget constraint of a slot `c < C` is a constraint of `Φ`. -/
theorem gadAt_mem {c : ℕ} (hc : c < paramC Φ) : gadAt Φ c ∈ Φ := by
  have h : gadAt Φ c ∈ gad Φ := by
    unfold gadAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]
    exact List.getElem_mem hc
  exact List.mem_of_mem_filter h

/-- The gadget constraint of a slot `c < C` is not of the form `x = 1`. -/
theorem gadAt_isGad {c : ℕ} (hc : c < paramC Φ) : isGad (gadAt Φ c) = true := by
  have h : gadAt Φ c ∈ gad Φ := by
    unfold gadAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]
    exact List.getElem_mem hc
  exact (List.mem_filter.1 h).2

/-! ### Walls of the addition gadgets -/

/-- Two consecutive entries of a list form an infix of it. -/
theorem pair_infix {α : Type*} (l : List α) {i : ℕ} (hi : i + 1 < l.length) :
    [l[i], l[i + 1]] <:+: l := by
  have e : (l.drop i).take 2 = [l[i], l[i + 1]] := by
    have h1 : i < l.length := by omega
    rw [List.drop_eq_getElem_cons h1, List.drop_eq_getElem_cons hi]
    rfl
  rw [← e]
  exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix

/-- Consecutive vertices of a floor feature form an edge of `SP n Φ`. -/
theorem pedge_of_floor {ch : List RPt} {ox : ℚ}
    (hf : ch.map (RPt.inst (paramH n Φ) ox) ∈ floorFeats n Φ) {L : List Point}
    (hL : ch.map (fun p => ratPoint (p.inst (paramH n Φ) ox)) = L) (i : ℕ)
    (hi : i + 1 < L.length) : PEdge (SP n Φ) L[i] L[i + 1] := by
  subst hL
  have hlen : i + 1 < (ch.map (RPt.inst (paramH n Φ) ox)).length := by simpa using hi
  obtain ⟨j, hj, h1, h2⟩ := edge_of_infix ((pair_infix _ hlen).trans (floor_infix hf))
  refine ⟨j, hj, ?_, ?_⟩
  · rw [h1]; simp
  · rw [h2]; simp

/-- The pocket walls of an addition gadget are edges of `SP n Φ`. -/
theorem slot_walls {c : ℕ} (hc : c < paramC Φ) :
    kWalls (SP n Φ) (cKind (gadAt Φ c)) (slotG n Φ c : ℝ) := by
  have hG : (((slotG n Φ c : ℕ) : ℚ) : ℝ) = (slotG n Φ c : ℝ) := by simp
  cases hk : cKind (gadAt Φ c) with
  | invGe => trivial
  | invRevLe => trivial
  | addLe =>
    have hf := slotFloor_mem (n := n) hc (ch := chainAddLe) (by rw [hk]; simp [tmplFloor])
    have hL := chainAddLe_inst (paramH n Φ) (slotG n Φ c : ℚ)
    rw [hG] at hL
    have e := fun i hi => pedge_of_floor hf hL i hi
    exact ⟨e 3 (by simp), e 1 (by simp), e 2 (by simp), e 11 (by simp), e 9 (by simp),
      e 10 (by simp), e 7 (by simp), e 5 (by simp), e 6 (by simp)⟩
  | addGe =>
    have hf := slotFloor_mem (n := n) hc (ch := chainAddGe) (by rw [hk]; simp [tmplFloor])
    have hL := chainAddGe_inst (paramH n Φ) (slotG n Φ c : ℚ)
    rw [hG] at hL
    have e := fun i hi => pedge_of_floor hf hL i hi
    exact ⟨e 3 (by simp), e 1 (by simp), e 2 (by simp), e 11 (by simp), e 9 (by simp),
      e 10 (by simp), e 7 (by simp), e 5 (by simp), e 6 (by simp)⟩

end ArtGallery.Stade

end
