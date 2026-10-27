module

public import ArtGallery.Vis.API

/-!
# Visibility library: counting and pinning (tool T3, two-stage form)

The two-stage counting argument of `08_proof_plan.md` §5, stated abstractly over a finite type `ι`
of *positions*.  Every position `X` has a witness `m X` in the region, and the visibility sets of
the witnesses are pairwise disjoint (W2).

* **Lower bound** (`card_le_of_witnesses`): every guard set has at least `|ι|` guards.
* **Exact count** (`exists_witness_of_card_eq`, `eq_of_sees_witness`): a guard set with exactly
  `|ι|` guards has every guard seeing a witness, and the guard seeing `m X` is unique.
* **Pinning** (`pinned_of_card_eq`): let `W X` be the witness set of `X` and `Spot X` a set
  containing every point of the region that sees all of `W X` (W1).  Positions are processed along
  a well-founded relation `r` (`r Y X`: `Y` is processed before `X`).  If for `Y ≠ X` the points
  of `Spot Y` seeing `m Y` see no `w ∈ W X` when `Y` comes before `X`, and no point seeing `m Y`
  sees any `w ∈ W X` otherwise (W3), then, for a guard set of exactly `|ι|` guards, the guard
  seeing `m X` lies in `Spot X`.  `guards_pinned` summarises the conclusion.

All statements come in a form with an **allowed set** `Ω` of guard positions (suffix `_on`): the
guards lie in `Ω` (`↑G ⊆ Ω`), they see every point of the region, and the conditions on points
(W1, W2, W3) are only required for points of `Ω`.  The statements without suffix are the case
`Ω = P.filled`, i.e. guard sets (`IsGuardSet`); `Ω = P.boundary` gives guard sets on the boundary
(`IsGuardSetOnBoundary`).
-/

@[expose] public section

namespace ArtGallery

namespace Polygon

open Set

variable {P : Polygon} {ι : Type*} [Fintype ι]

/-- A guard of `G` for each witness. -/
theorem exists_guard_sees {G : Finset Point} (hG : P.IsGuardSet (G : Set Point)) {q : Point}
    (hq : q ∈ P.filled) : ∃ g ∈ G, P.Sees g q := by
  obtain ⟨g, hg, hgq⟩ := hG.2 q hq
  exact ⟨g, hg, hgq⟩

/-! ### Guards in an allowed set `Ω` -/

section On

variable {G : Finset Point} {Ω : Set Point}

/-- **Lower bound (W2), allowed set `Ω`.** If the witnesses `m X` (`X : ι`) lie in the region and
no point of `Ω` sees two of them, every set of guards in `Ω` seeing the region has at least `|ι|`
guards. -/
theorem card_le_of_witnesses_on (hGΩ : (G : Set Point) ⊆ Ω)
    (hcov : ∀ q ∈ P.filled, ∃ g ∈ (G : Set Point), P.Sees g q)
    (m : ι → Point) (hm : ∀ X, m X ∈ P.filled)
    (hdisj : ∀ X Y, X ≠ Y → ∀ p ∈ Ω, P.Sees p (m X) → ¬ P.Sees p (m Y)) :
    Fintype.card ι ≤ G.card := by
  classical
  choose g hgG hgs using fun X => hcov (m X) (hm X)
  have hinj : Set.InjOn g (Finset.univ : Finset ι) := by
    intro X _ Y _ hXY
    by_contra hne
    exact hdisj X Y hne (g X) (hGΩ (hgG X)) (hgs X) (hXY ▸ hgs Y)
  have := Finset.card_le_card_of_injOn g (fun X _ => Finset.mem_coe.1 (hgG X)) hinj
  simpa using this

/-- The guards are the guards of the witnesses (exact count, allowed set `Ω`). -/
private theorem image_eq_on (hGΩ : (G : Set Point) ⊆ Ω)
    (m : ι → Point) (hdisj : ∀ X Y, X ≠ Y → ∀ p ∈ Ω, P.Sees p (m X) → ¬ P.Sees p (m Y))
    (hcard : G.card = Fintype.card ι) (g : ι → Point) (hgG : ∀ X, g X ∈ (G : Set Point))
    (hgs : ∀ X, P.Sees (g X) (m X)) [DecidableEq Point] :
    Set.InjOn g (Finset.univ : Finset ι) ∧ Finset.univ.image g = G := by
  have hinj : Set.InjOn g (Finset.univ : Finset ι) := by
    intro X _ Y _ hXY
    by_contra hne
    exact hdisj X Y hne (g X) (hGΩ (hgG X)) (hgs X) (hXY ▸ hgs Y)
  have hsub : Finset.univ.image g ⊆ G := by
    intro q hq
    obtain ⟨X, -, rfl⟩ := Finset.mem_image.1 hq
    exact hgG X
  refine ⟨hinj, Finset.eq_of_subset_of_card_le hsub ?_⟩
  rw [Finset.card_image_of_injOn hinj, hcard, Finset.card_univ]

/-- **Exact count, existence, allowed set `Ω`.** If the guard set has exactly `|ι|` guards, every
guard sees some witness. -/
theorem exists_witness_of_card_eq_on (hGΩ : (G : Set Point) ⊆ Ω)
    (hcov : ∀ q ∈ P.filled, ∃ g ∈ (G : Set Point), P.Sees g q)
    (m : ι → Point) (hm : ∀ X, m X ∈ P.filled)
    (hdisj : ∀ X Y, X ≠ Y → ∀ p ∈ Ω, P.Sees p (m X) → ¬ P.Sees p (m Y))
    (hcard : G.card = Fintype.card ι) : ∀ q ∈ G, ∃ X, P.Sees q (m X) := by
  classical
  choose g hgG hgs using fun X => hcov (m X) (hm X)
  have heq := (image_eq_on hGΩ m hdisj hcard g hgG hgs).2
  intro q hq
  rw [← heq] at hq
  obtain ⟨X, -, rfl⟩ := Finset.mem_image.1 hq
  exact ⟨X, hgs X⟩

/-- **Exact count, uniqueness, allowed set `Ω`.** If the guard set has exactly `|ι|` guards, two
guards seeing the same witness are equal. -/
theorem eq_of_sees_witness_on (hGΩ : (G : Set Point) ⊆ Ω)
    (hcov : ∀ q ∈ P.filled, ∃ g ∈ (G : Set Point), P.Sees g q)
    (m : ι → Point) (hm : ∀ X, m X ∈ P.filled)
    (hdisj : ∀ X Y, X ≠ Y → ∀ p ∈ Ω, P.Sees p (m X) → ¬ P.Sees p (m Y))
    (hcard : G.card = Fintype.card ι) {X : ι} {q q' : Point} (hq : q ∈ G) (hq' : q' ∈ G)
    (hs : P.Sees q (m X)) (hs' : P.Sees q' (m X)) : q = q' := by
  classical
  choose g hgG hgs using fun X => hcov (m X) (hm X)
  have heq := (image_eq_on hGΩ m hdisj hcard g hgG hgs).2
  -- every guard seeing `m X` is `g X`
  have key : ∀ q ∈ G, P.Sees q (m X) → q = g X := by
    intro q hq hs
    rw [← heq] at hq
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hq
    by_cases hYX : Y = X
    · rw [hYX]
    · exact absurd hs (hdisj Y X hYX (g Y) (hGΩ (hgG Y)) (hgs Y))
  rw [key q hq hs, key q' hq' hs']

/-- **Pinning (two-stage counting), allowed set `Ω`.** For a set of exactly `|ι|` guards in `Ω`
seeing the region, positions processed along the well-founded relation `r`: the guard seeing the
witness `m X` lies in `Spot X`, provided
* (W1) every point of `Ω` seeing all of `W X` lies in `Spot X`;
* (W3, earlier positions) for `Y ≠ X` with `r Y X`, no point of `Spot Y ∩ Ω` seeing `m Y` sees a
  point of `W X`;
* (W3, other positions) for `Y ≠ X` with `¬ r Y X`, no point of `Ω` sees both `m Y` and a point
  of `W X`. -/
theorem pinned_of_card_eq_on (hGΩ : (G : Set Point) ⊆ Ω)
    (hcov : ∀ q ∈ P.filled, ∃ g ∈ (G : Set Point), P.Sees g q)
    (m : ι → Point) (hm : ∀ X, m X ∈ P.filled)
    (hdisj : ∀ X Y, X ≠ Y → ∀ p ∈ Ω, P.Sees p (m X) → ¬ P.Sees p (m Y))
    (hcard : G.card = Fintype.card ι) (W : ι → Set Point) (hW : ∀ X, W X ⊆ P.filled)
    (Spot : ι → Set Point) (hSpot : ∀ X, ∀ p ∈ Ω, (∀ w ∈ W X, P.Sees p w) → p ∈ Spot X)
    (r : ι → ι → Prop) (hr : WellFounded r)
    (hearly : ∀ X Y, Y ≠ X → r Y X → ∀ w ∈ W X, ∀ p ∈ Ω, p ∈ Spot Y →
      P.Sees p (m Y) → ¬ P.Sees p w)
    (hlate : ∀ X Y, Y ≠ X → ¬ r Y X → ∀ w ∈ W X, ∀ p ∈ Ω, P.Sees p (m Y) →
      ¬ P.Sees p w) :
    ∀ X, ∀ q ∈ G, P.Sees q (m X) → q ∈ Spot X := by
  intro X
  induction X using hr.induction with
  | _ X ih =>
    intro q hq hqX
    refine hSpot X q (hGΩ hq) fun w hw => ?_
    obtain ⟨q', hq', hq'w⟩ := hcov w (hW X hw)
    obtain ⟨Y, hq'Y⟩ := exists_witness_of_card_eq_on hGΩ hcov m hm hdisj hcard q' hq'
    by_cases hYX : Y = X
    · subst hYX
      rw [eq_of_sees_witness_on hGΩ hcov m hm hdisj hcard hq hq' hqX hq'Y]
      exact hq'w
    · by_cases hrYX : r Y X
      · exact absurd hq'w (hearly X Y hYX hrYX w hw q' (hGΩ hq') (ih Y hrYX q' hq' hq'Y) hq'Y)
      · exact absurd hq'w (hlate X Y hYX hrYX w hw q' (hGΩ hq') hq'Y)

/-- **Pinning, summary, allowed set `Ω`.** Under the hypotheses of `pinned_of_card_eq_on`, every
position `X` has a unique guard seeing `m X`, it lies in `Spot X`, and every guard is the guard of
some position. -/
theorem guards_pinned_on (hGΩ : (G : Set Point) ⊆ Ω)
    (hcov : ∀ q ∈ P.filled, ∃ g ∈ (G : Set Point), P.Sees g q)
    (m : ι → Point) (hm : ∀ X, m X ∈ P.filled)
    (hdisj : ∀ X Y, X ≠ Y → ∀ p ∈ Ω, P.Sees p (m X) → ¬ P.Sees p (m Y))
    (hcard : G.card = Fintype.card ι) (W : ι → Set Point) (hW : ∀ X, W X ⊆ P.filled)
    (Spot : ι → Set Point) (hSpot : ∀ X, ∀ p ∈ Ω, (∀ w ∈ W X, P.Sees p w) → p ∈ Spot X)
    (r : ι → ι → Prop) (hr : WellFounded r)
    (hearly : ∀ X Y, Y ≠ X → r Y X → ∀ w ∈ W X, ∀ p ∈ Ω, p ∈ Spot Y →
      P.Sees p (m Y) → ¬ P.Sees p w)
    (hlate : ∀ X Y, Y ≠ X → ¬ r Y X → ∀ w ∈ W X, ∀ p ∈ Ω, P.Sees p (m Y) →
      ¬ P.Sees p w) :
    (∀ X, ∃ q ∈ G, P.Sees q (m X) ∧ q ∈ Spot X ∧ ∀ q' ∈ G, P.Sees q' (m X) → q' = q) ∧
      (∀ q ∈ G, ∃ X, P.Sees q (m X) ∧ q ∈ Spot X) := by
  have hpin := pinned_of_card_eq_on hGΩ hcov m hm hdisj hcard W hW Spot hSpot r hr hearly hlate
  refine ⟨fun X => ?_, fun q hq => ?_⟩
  · obtain ⟨q, hq, hqX⟩ := hcov (m X) (hm X)
    exact ⟨q, hq, hqX, hpin X q hq hqX,
      fun q' hq' hq'X => eq_of_sees_witness_on hGΩ hcov m hm hdisj hcard hq' hq hq'X hqX⟩
  · obtain ⟨X, hqX⟩ := exists_witness_of_card_eq_on hGΩ hcov m hm hdisj hcard q hq
    exact ⟨X, hqX, hpin X q hq hqX⟩

end On

/-! ### Guard sets (`Ω = P.filled`) -/

/-- **Lower bound (W2).** If the witnesses `m X` (`X : ι`) lie in the region and no point of the
region sees two of them, every guard set has at least `|ι|` guards. -/
theorem card_le_of_witnesses (G : Finset Point) (hG : P.IsGuardSet (G : Set Point))
    (m : ι → Point) (hm : ∀ X, m X ∈ P.filled)
    (hdisj : ∀ X Y, X ≠ Y → ∀ p ∈ P.filled, P.Sees p (m X) → ¬ P.Sees p (m Y)) :
    Fintype.card ι ≤ G.card :=
  card_le_of_witnesses_on hG.1 hG.2 m hm hdisj

/-- **Exact count, existence.** If the guard set has exactly `|ι|` guards, every guard sees some
witness. -/
theorem exists_witness_of_card_eq (G : Finset Point) (hG : P.IsGuardSet (G : Set Point))
    (m : ι → Point) (hm : ∀ X, m X ∈ P.filled)
    (hdisj : ∀ X Y, X ≠ Y → ∀ p ∈ P.filled, P.Sees p (m X) → ¬ P.Sees p (m Y))
    (hcard : G.card = Fintype.card ι) : ∀ q ∈ G, ∃ X, P.Sees q (m X) :=
  exists_witness_of_card_eq_on hG.1 hG.2 m hm hdisj hcard

/-- **Exact count, uniqueness.** If the guard set has exactly `|ι|` guards, two guards seeing the
same witness are equal. -/
theorem eq_of_sees_witness (G : Finset Point) (hG : P.IsGuardSet (G : Set Point))
    (m : ι → Point) (hm : ∀ X, m X ∈ P.filled)
    (hdisj : ∀ X Y, X ≠ Y → ∀ p ∈ P.filled, P.Sees p (m X) → ¬ P.Sees p (m Y))
    (hcard : G.card = Fintype.card ι) {X : ι} {q q' : Point} (hq : q ∈ G) (hq' : q' ∈ G)
    (hs : P.Sees q (m X)) (hs' : P.Sees q' (m X)) : q = q' :=
  eq_of_sees_witness_on hG.1 hG.2 m hm hdisj hcard hq hq' hs hs'

/-- **Pinning (two-stage counting).** For a guard set with exactly `|ι|` guards, positions
processed along the well-founded relation `r`: the guard seeing the witness `m X` lies in
`Spot X`, provided
* (W1) every point of the region seeing all of `W X` lies in `Spot X`;
* (W3, earlier positions) for `Y ≠ X` with `r Y X`, no point of `Spot Y ∩ P.filled` seeing `m Y`
  sees a point of `W X`;
* (W3, other positions) for `Y ≠ X` with `¬ r Y X`, no point of the region sees both `m Y` and a
  point of `W X`. -/
theorem pinned_of_card_eq (G : Finset Point) (hG : P.IsGuardSet (G : Set Point))
    (m : ι → Point) (hm : ∀ X, m X ∈ P.filled)
    (hdisj : ∀ X Y, X ≠ Y → ∀ p ∈ P.filled, P.Sees p (m X) → ¬ P.Sees p (m Y))
    (hcard : G.card = Fintype.card ι) (W : ι → Set Point) (hW : ∀ X, W X ⊆ P.filled)
    (Spot : ι → Set Point) (hSpot : ∀ X, ∀ p ∈ P.filled, (∀ w ∈ W X, P.Sees p w) → p ∈ Spot X)
    (r : ι → ι → Prop) (hr : WellFounded r)
    (hearly : ∀ X Y, Y ≠ X → r Y X → ∀ w ∈ W X, ∀ p ∈ P.filled, p ∈ Spot Y →
      P.Sees p (m Y) → ¬ P.Sees p w)
    (hlate : ∀ X Y, Y ≠ X → ¬ r Y X → ∀ w ∈ W X, ∀ p ∈ P.filled, P.Sees p (m Y) →
      ¬ P.Sees p w) :
    ∀ X, ∀ q ∈ G, P.Sees q (m X) → q ∈ Spot X :=
  pinned_of_card_eq_on hG.1 hG.2 m hm hdisj hcard W hW Spot hSpot r hr hearly hlate

/-- **Pinning, summary.** Under the hypotheses of `pinned_of_card_eq`, every position `X` has a
unique guard seeing `m X`, it lies in `Spot X`, and every guard is the guard of some position. -/
theorem guards_pinned (G : Finset Point) (hG : P.IsGuardSet (G : Set Point))
    (m : ι → Point) (hm : ∀ X, m X ∈ P.filled)
    (hdisj : ∀ X Y, X ≠ Y → ∀ p ∈ P.filled, P.Sees p (m X) → ¬ P.Sees p (m Y))
    (hcard : G.card = Fintype.card ι) (W : ι → Set Point) (hW : ∀ X, W X ⊆ P.filled)
    (Spot : ι → Set Point) (hSpot : ∀ X, ∀ p ∈ P.filled, (∀ w ∈ W X, P.Sees p w) → p ∈ Spot X)
    (r : ι → ι → Prop) (hr : WellFounded r)
    (hearly : ∀ X Y, Y ≠ X → r Y X → ∀ w ∈ W X, ∀ p ∈ P.filled, p ∈ Spot Y →
      P.Sees p (m Y) → ¬ P.Sees p w)
    (hlate : ∀ X Y, Y ≠ X → ¬ r Y X → ∀ w ∈ W X, ∀ p ∈ P.filled, P.Sees p (m Y) →
      ¬ P.Sees p w) :
    (∀ X, ∃ q ∈ G, P.Sees q (m X) ∧ q ∈ Spot X ∧ ∀ q' ∈ G, P.Sees q' (m X) → q' = q) ∧
      (∀ q ∈ G, ∃ X, P.Sees q (m X) ∧ q ∈ Spot X) :=
  guards_pinned_on hG.1 hG.2 m hm hdisj hcard W hW Spot hSpot r hr hearly hlate

end Polygon

end ArtGallery

end
