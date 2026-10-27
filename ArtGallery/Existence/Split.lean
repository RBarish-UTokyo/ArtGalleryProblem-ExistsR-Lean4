module

public import ArtGallery.Jordan.Jordan

/-!
# The abstract splitting lemma

Let `P`, `Q₁`, `Q₂` be simple polygons such that

* the boundaries of `Q₁` and `Q₂` lie in the filled region of `P` (`hb`),
* the boundary of `P` lies in the union of the boundaries of `Q₁` and `Q₂` (`hb'`),
* a point off all three boundaries is filled in `P` exactly when it is filled in exactly one
  of `Q₁`, `Q₂` (`hxor`).

Then (`split_filled`)

* `P.filled = Q₁.filled ∪ Q₂.filled`,
* the interiors of `Q₁.filled` and `Q₂.filled` are disjoint,
* `Q₁.filled ∩ Q₂.filled ⊆ Q₁.boundary ∩ Q₂.boundary`.

The proof: the common interior `I = (Q₁.filled \ Q₁.boundary) ∩ (Q₂.filled \ Q₂.boundary)` is
open, lies in `P.filledᶜ` (by `hxor`) and is relatively closed there (the filled regions are
closed, and a boundary point of `Q_i` is in `P.filled`); since `P.filledᶜ` is connected and
unbounded while `I` is bounded, `I = ∅`.  The remaining claims follow from `I = ∅` using
`boundary_subset_closure_interior`.

Provenance: adapted from `Chazelle/Existence/Split.lean` of the Palomar entry
PALOMAR-2026-10-05-000003 (`LinearTimeTriangulation-ChazelleAlgorithm-Lean4`, commit
`92cc7745aa02`, Apache-2.0);
the namespace `Chazelle` is renamed to `ArtGallery`.
-/

namespace ArtGallery.Existence

@[expose] public section

open Set Topology
open ArtGallery.Jordan

/-- The filled region of a simple polygon lies in the closure of its interior. -/
theorem filled_subset_closure_interior {Q : Polygon} (hQ : Q.Simple) :
    Q.filled ⊆ closure (Q.filled \ Q.boundary) := by
  intro z hz
  by_cases hzb : z ∈ Q.boundary
  · exact boundary_subset_closure_interior hQ hzb
  · exact subset_closure ⟨hz, hzb⟩

/-- If the interiors of two simple polygons do not meet, then their filled regions meet only in
points of both boundaries. -/
theorem filled_inter_subset_of_interior_disjoint {Q₁ Q₂ : Polygon} (h₁ : Q₁.Simple)
    (h₂ : Q₂.Simple)
    (hI : (Q₁.filled \ Q₁.boundary) ∩ (Q₂.filled \ Q₂.boundary) = ∅) :
    Q₁.filled ∩ Q₂.filled ⊆ Q₁.boundary ∩ Q₂.boundary := by
  rintro z ⟨hz₁, hz₂⟩
  have key : ∀ (A B : Polygon), A.Simple → B.Simple →
      (A.filled \ A.boundary) ∩ (B.filled \ B.boundary) = ∅ →
      z ∈ A.filled → z ∈ B.filled → z ∈ A.boundary := by
    intro A B hA hB hAB hzA hzB
    by_contra hzb
    have hopen : IsOpen (A.filled \ A.boundary) := isOpen_filled_sdiff_boundary hA
    have hnhds : A.filled \ A.boundary ∈ 𝓝 z := hopen.mem_nhds ⟨hzA, hzb⟩
    have hcl : z ∈ closure (B.filled \ B.boundary) := filled_subset_closure_interior hB hzB
    obtain ⟨y, hy⟩ := mem_closure_iff_nhds.1 hcl _ hnhds
    have : y ∈ (A.filled \ A.boundary) ∩ (B.filled \ B.boundary) := hy
    rw [hAB] at this
    exact this
  refine ⟨key Q₁ Q₂ h₁ h₂ hI hz₁ hz₂, key Q₂ Q₁ h₂ h₁ ?_ hz₂ hz₁⟩
  rw [inter_comm]; exact hI

/-- The exterior of a simple polygon is not contained in the filled region of any polygon. -/
theorem filled_compl_not_subset_filled (P Q : Polygon) : ¬ P.filledᶜ ⊆ Q.filled := by
  intro h
  set w : Point := (max (coordBound P) (coordBound Q) + 1, 0) with hw
  have hP : coordBound P < w.1 := by
    simp only [hw]; linarith [le_max_left (coordBound P) (coordBound Q)]
  have hQ : coordBound Q < w.1 := by
    simp only [hw]; linarith [le_max_right (coordBound P) (coordBound Q)]
  exact far_not_mem_filled Q (Or.inl hQ) (h (far_not_mem_filled P (Or.inl hP)))

/-- **The common interior is empty.**  Under the hypotheses of the splitting lemma, the
interiors of `Q₁` and `Q₂` do not meet. -/
theorem common_interior_empty {P Q₁ Q₂ : Polygon} (hP : P.Simple) (h₁ : Q₁.Simple)
    (h₂ : Q₂.Simple) (hb : Q₁.boundary ∪ Q₂.boundary ⊆ P.filled)
    (hb' : P.boundary ⊆ Q₁.boundary ∪ Q₂.boundary)
    (hxor : ∀ z, z ∉ P.boundary → z ∉ Q₁.boundary → z ∉ Q₂.boundary →
      (z ∈ P.filled ↔ (z ∈ Q₁.filled ↔ z ∉ Q₂.filled))) :
    (Q₁.filled \ Q₁.boundary) ∩ (Q₂.filled \ Q₂.boundary) = ∅ := by
  set I := (Q₁.filled \ Q₁.boundary) ∩ (Q₂.filled \ Q₂.boundary) with hIdef
  -- `I` lies in the exterior of `P`
  have hIP : I ⊆ P.filledᶜ := by
    rintro z ⟨⟨hz₁, hz₁b⟩, ⟨hz₂, hz₂b⟩⟩
    have hzP : z ∉ P.boundary := fun h => (hb' h).elim hz₁b hz₂b
    intro hzf
    have := (hxor z hzP hz₁b hz₂b).1 hzf
    exact (this.1 hz₁) hz₂
  -- `I` is open
  have hIopen : IsOpen I :=
    (isOpen_filled_sdiff_boundary h₁).inter (isOpen_filled_sdiff_boundary h₂)
  -- `I` is relatively closed in the exterior of `P`
  have hIcl : closure I ∩ P.filledᶜ ⊆ I := by
    rintro z ⟨hzc, hzP⟩
    have hz₁ : z ∈ Q₁.filled :=
      (isClosed_filled Q₁).closure_subset (closure_mono (fun _ h => h.1.1) hzc)
    have hz₂ : z ∈ Q₂.filled :=
      (isClosed_filled Q₂).closure_subset (closure_mono (fun _ h => h.2.1) hzc)
    refine ⟨⟨hz₁, fun h => hzP (hb (Or.inl h))⟩, ⟨hz₂, fun h => hzP (hb (Or.inr h))⟩⟩
  -- connectedness of the exterior
  by_contra hne
  rw [← Ne, ← nonempty_iff_ne_empty] at hne
  obtain ⟨z, hz⟩ := hne
  have hVopen : IsOpen (P.filledᶜ ∩ (closure I)ᶜ) :=
    (isOpen_filled_compl P).inter isClosed_closure.isOpen_compl
  have hdisj : Disjoint I (P.filledᶜ ∩ (closure I)ᶜ) :=
    Set.disjoint_left.2 fun x hx hx' => hx'.2 (subset_closure hx)
  have hcov : P.filledᶜ ⊆ I ∪ (P.filledᶜ ∩ (closure I)ᶜ) := by
    intro x hx
    by_cases hxc : x ∈ closure I
    · exact Or.inl (hIcl ⟨hxc, hx⟩)
    · exact Or.inr ⟨hx, hxc⟩
  have hsub : P.filledᶜ ⊆ I :=
    IsPreconnected.subset_left_of_subset_union hIopen hVopen hdisj hcov ⟨z, hIP hz, hz⟩
      (filled_compl_connected hP)
  exact filled_compl_not_subset_filled P Q₁ (fun x hx => (hsub hx).1.1)

/-- **The splitting lemma.**  Let `P`, `Q₁`, `Q₂` be simple polygons with the boundaries of
`Q₁`, `Q₂` inside `P.filled`, the boundary of `P` inside the union of the boundaries of `Q₁`
and `Q₂`, and such that every point off all three boundaries is filled in `P` exactly when it
is filled in exactly one of `Q₁`, `Q₂`.  Then the filled region of `P` is the union of the
filled regions of `Q₁` and `Q₂`, the interiors of the latter are disjoint, and the filled
regions of `Q₁` and `Q₂` meet only in points of both boundaries. -/
theorem split_filled {P Q₁ Q₂ : Polygon} (hP : P.Simple) (h₁ : Q₁.Simple) (h₂ : Q₂.Simple)
    (hb : Q₁.boundary ∪ Q₂.boundary ⊆ P.filled)
    (hb' : P.boundary ⊆ Q₁.boundary ∪ Q₂.boundary)
    (hxor : ∀ z, z ∉ P.boundary → z ∉ Q₁.boundary → z ∉ Q₂.boundary →
      (z ∈ P.filled ↔ (z ∈ Q₁.filled ↔ z ∉ Q₂.filled))) :
    P.filled = Q₁.filled ∪ Q₂.filled ∧
      Disjoint (interior Q₁.filled) (interior Q₂.filled) ∧
      Q₁.filled ∩ Q₂.filled ⊆ Q₁.boundary ∩ Q₂.boundary := by
  have hI := common_interior_empty hP h₁ h₂ hb hb' hxor
  have hmeet := filled_inter_subset_of_interior_disjoint h₁ h₂ hI
  refine ⟨?_, ?_, hmeet⟩
  · apply Subset.antisymm
    · intro z hz
      by_cases hzP : z ∈ P.boundary
      · rcases hb' hzP with h | h
        · exact Or.inl (boundary_subset_filled Q₁ h)
        · exact Or.inr (boundary_subset_filled Q₂ h)
      by_cases hz₁ : z ∈ Q₁.boundary
      · exact Or.inl (boundary_subset_filled Q₁ hz₁)
      by_cases hz₂ : z ∈ Q₂.boundary
      · exact Or.inr (boundary_subset_filled Q₂ hz₂)
      have h := (hxor z hzP hz₁ hz₂).1 hz
      by_cases hz₁f : z ∈ Q₁.filled
      · exact Or.inl hz₁f
      · exact Or.inr (by_contra fun h' => hz₁f (h.2 h'))
    · intro z hz
      by_cases hzP : z ∈ P.boundary
      · exact boundary_subset_filled P hzP
      by_cases hz₁ : z ∈ Q₁.boundary
      · exact hb (Or.inl hz₁)
      by_cases hz₂ : z ∈ Q₂.boundary
      · exact hb (Or.inr hz₂)
      have h := hxor z hzP hz₁ hz₂
      rcases hz with hzf | hzf
      · have hz₂f : z ∉ Q₂.filled := fun h' => hz₁ (hmeet ⟨hzf, h'⟩).1
        exact h.2 ⟨fun _ => hz₂f, fun _ => hzf⟩
      · have hz₁f : z ∉ Q₁.filled := fun h' => hz₂ (hmeet ⟨h', hzf⟩).2
        exact h.2 ⟨fun h' => absurd h' hz₁f, fun h' => absurd hzf h'⟩
  · rw [interior_filled h₁, interior_filled h₂, Set.disjoint_iff_inter_eq_empty]
    exact hI

/-- The filled region of `P` is the union of the filled regions of `Q₁` and `Q₂`
(first conclusion of `split_filled`). -/
theorem split_filled_eq_union {P Q₁ Q₂ : Polygon} (hP : P.Simple) (h₁ : Q₁.Simple)
    (h₂ : Q₂.Simple) (hb : Q₁.boundary ∪ Q₂.boundary ⊆ P.filled)
    (hb' : P.boundary ⊆ Q₁.boundary ∪ Q₂.boundary)
    (hxor : ∀ z, z ∉ P.boundary → z ∉ Q₁.boundary → z ∉ Q₂.boundary →
      (z ∈ P.filled ↔ (z ∈ Q₁.filled ↔ z ∉ Q₂.filled))) :
    P.filled = Q₁.filled ∪ Q₂.filled :=
  (split_filled hP h₁ h₂ hb hb' hxor).1

/-- The interiors of the filled regions of `Q₁` and `Q₂` are disjoint
(second conclusion of `split_filled`). -/
theorem split_interior_disjoint {P Q₁ Q₂ : Polygon} (hP : P.Simple) (h₁ : Q₁.Simple)
    (h₂ : Q₂.Simple) (hb : Q₁.boundary ∪ Q₂.boundary ⊆ P.filled)
    (hb' : P.boundary ⊆ Q₁.boundary ∪ Q₂.boundary)
    (hxor : ∀ z, z ∉ P.boundary → z ∉ Q₁.boundary → z ∉ Q₂.boundary →
      (z ∈ P.filled ↔ (z ∈ Q₁.filled ↔ z ∉ Q₂.filled))) :
    Disjoint (interior Q₁.filled) (interior Q₂.filled) :=
  (split_filled hP h₁ h₂ hb hb' hxor).2.1

/-- The filled regions of `Q₁` and `Q₂` meet only in points of both boundaries
(third conclusion of `split_filled`). -/
theorem split_filled_inter_subset {P Q₁ Q₂ : Polygon} (hP : P.Simple) (h₁ : Q₁.Simple)
    (h₂ : Q₂.Simple) (hb : Q₁.boundary ∪ Q₂.boundary ⊆ P.filled)
    (hb' : P.boundary ⊆ Q₁.boundary ∪ Q₂.boundary)
    (hxor : ∀ z, z ∉ P.boundary → z ∉ Q₁.boundary → z ∉ Q₂.boundary →
      (z ∈ P.filled ↔ (z ∈ Q₁.filled ↔ z ∉ Q₂.filled))) :
    Q₁.filled ∩ Q₂.filled ⊆ Q₁.boundary ∩ Q₂.boundary :=
  (split_filled hP h₁ h₂ hb hb' hxor).2.2

end

end ArtGallery.Existence
