module

public import ArtGallery.Geometry.SpecExtra
public import ArtGallery.Membership.Witness.Main

/-!
# The witness lemma (interface)

The heart of the proof that the art gallery problem is in `∃ℝ` (paper §3): finitely many
*witness points* — centroids of triples of vertices of a line arrangement determined by the
polygon and the guards — certify that a finite set of guards sees the whole polygon.

Lines are given by pairs of points (a pair of equal points gives no intersections).
-/

@[expose] public section

namespace ArtGallery.Membership

/-- The intersection point of the lines through `l₁` and through `l₂`, when their direction
vectors are not parallel (in particular both lines are well defined). -/
noncomputable def lineInter (l₁ l₂ : Point × Point) : Option Point :=
  let d₁ : Point := l₁.2 - l₁.1
  let d₂ : Point := l₂.2 - l₂.1
  let D := d₁.1 * d₂.2 - d₁.2 * d₂.1
  if D = 0 then none
  else
    let c₁ := l₁.1.1 * l₁.2.2 - l₁.1.2 * l₁.2.1
    let c₂ := l₂.1.1 * l₂.2.2 - l₂.1.2 * l₂.2.1
    some ((c₂ * d₁.1 - c₁ * d₂.1) / D, (c₂ * d₁.2 - c₁ * d₂.2) / D)

/-- The lines of the arrangement: the lines of the edges of `P` and the lines through a guard
and a vertex. -/
def arrangementLines (P : Polygon) (Γ : List Point) : List (Point × Point) :=
  (List.range P.n).map (fun j => (P.vtx j, P.vtx ((j + 1) % P.n))) ++
    Γ.flatMap (fun γ => (List.range P.n).map (fun k => (γ, P.vtx k)))

/-- The vertices of the arrangement: intersection points of two non-parallel lines. -/
def arrangementVertices (L : List (Point × Point)) : Set Point :=
  {x | ∃ l₁ ∈ L, ∃ l₂ ∈ L, lineInter l₁ l₂ = some x}

/-- The centroid of three points. -/
noncomputable def centroid (a b c : Point) : Point :=
  ((a.1 + b.1 + c.1) / 3, (a.2 + b.2 + c.2) / 3)

/-- **Witness lemma.** If every centroid of three arrangement vertices that lies in the region is
seen by one of the guards (all lying in the region), then the guards see the whole region. -/
theorem guards_of_witnesses {P : Polygon} (hP : P.Simple) (Γ : List Point)
    (hΓ : ∀ γ ∈ Γ, γ ∈ P.filled)
    (h : ∀ a ∈ arrangementVertices (arrangementLines P Γ),
      ∀ b ∈ arrangementVertices (arrangementLines P Γ),
      ∀ c ∈ arrangementVertices (arrangementLines P Γ),
        centroid a b c ∈ P.filled → ∃ γ ∈ Γ, P.Sees γ (centroid a b c)) :
    ∀ p ∈ P.filled, ∃ γ ∈ Γ, P.Sees γ p := by
  refine Witness.guards_of_witnesses_core hP Γ hΓ (arrangementLines P Γ) ?_ ?_
    (arrangementVertices (arrangementLines P Γ)) ?_ h
  · intro j hj
    exact List.mem_append_left _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  · intro γ hγ k hk
    exact List.mem_append_right _
      (List.mem_flatMap.2 ⟨γ, hγ, List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩⟩)
  · -- `lineInter` computes the intersection point of two non-parallel lines
    intro ℓ₁ h₁ ℓ₂ h₂ x hD e₁ e₂
    refine ⟨ℓ₁, h₁, ℓ₂, h₂, ?_⟩
    simp only [lineInter]
    rw [ite_eq_right hD]
    simp only [Prod.fst_sub, Prod.snd_sub] at hD ⊢
    unfold det at e₁ e₂
    refine congrArg some (Prod.ext ?_ ?_)
    · simp only
      rw [div_eq_iff hD]
      linear_combination (ℓ₁.2.1 - ℓ₁.1.1) * e₂ - (ℓ₂.2.1 - ℓ₂.1.1) * e₁
    · simp only
      rw [div_eq_iff hD]
      linear_combination (ℓ₁.2.2 - ℓ₁.1.2) * e₂ - (ℓ₂.2.2 - ℓ₂.1.2) * e₁

end ArtGallery.Membership

end
